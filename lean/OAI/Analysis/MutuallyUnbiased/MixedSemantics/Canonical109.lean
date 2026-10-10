import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13952step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13952 raw13952Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw13952 raw13952Labels = mixedMoment B raw13952step0 raw13952step0Labels := by
      have hz : ∀ j, raw13952 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13952step0 = (fun i j => raw13952 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13952step0 raw13952; decide +kernel
      have hl : raw13952step0Labels = raw13952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13952 raw13952Labels permutation265 hz
    mixedMoment B raw13952step0 raw13952step0Labels = mixedMoment B raw13952step1 raw13952step1Labels := by
      have ha : raw13952step1 = (fun i j => raw13952step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13952step1 raw13952step0; decide +kernel
      have hl : raw13952step1Labels = raw13952step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13952step0 raw13952step0Labels permutation51 permutation7
    mixedMoment B raw13952step1 raw13952step1Labels = mixedMoment B raw13952step2 raw13952step2Labels := by
      have ha : raw13952step2 = -raw13952step1 := by apply Matrix.ext; change ∀ i j, raw13952step2 i j = -(raw13952step1 i j); unfold raw13952step2 raw13952step1; decide +kernel
      have hl : raw13952step2Labels = raw13952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13952step2 raw13952step2Labels = mixedMoment B raw13952step3 raw13952step3Labels := by
      have ha : raw13952step3 = raw13952step2 := by apply Matrix.ext; unfold raw13952step3 raw13952step2; decide +kernel
      have hl : raw13952step2Labels = labelEmbedding1 ∘ raw13952step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13952step2 raw13952step2Labels raw13952step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw13953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13953step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13953step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13953step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13953 raw13953Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw13953 raw13953Labels = mixedMoment B raw13953step0 raw13953step0Labels := by
      have hz : ∀ j, raw13953 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13953step0 = (fun i j => raw13953 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13953step0 raw13953; decide +kernel
      have hl : raw13953step0Labels = raw13953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13953 raw13953Labels permutation265 hz
    mixedMoment B raw13953step0 raw13953step0Labels = mixedMoment B raw13953step1 raw13953step1Labels := by
      have ha : raw13953step1 = (fun i j => raw13953step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13953step1 raw13953step0; decide +kernel
      have hl : raw13953step1Labels = raw13953step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13953step0 raw13953step0Labels permutation51 permutation7
    mixedMoment B raw13953step1 raw13953step1Labels = mixedMoment B raw13953step2 raw13953step2Labels := by
      have ha : raw13953step2 = -raw13953step1 := by apply Matrix.ext; change ∀ i j, raw13953step2 i j = -(raw13953step1 i j); unfold raw13953step2 raw13953step1; decide +kernel
      have hl : raw13953step2Labels = raw13953step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13953step2 raw13953step2Labels = mixedMoment B raw13953step3 raw13953step3Labels := by
      have ha : raw13953step3 = raw13953step2 := by apply Matrix.ext; unfold raw13953step3 raw13953step2; decide +kernel
      have hl : raw13953step2Labels = labelEmbedding1 ∘ raw13953step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13953step2 raw13953step2Labels raw13953step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw13954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13954step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13954step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13954step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw13954step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13954step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13954step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13954step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13954step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13954 raw13954Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw13954 raw13954Labels = mixedMoment B raw13954step0 raw13954step0Labels := by
      have hz : ∀ j, raw13954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13954step0 = (fun i j => raw13954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13954step0 raw13954; decide +kernel
      have hl : raw13954step0Labels = raw13954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13954 raw13954Labels permutation346 hz
    mixedMoment B raw13954step0 raw13954step0Labels = mixedMoment B raw13954step1 raw13954step1Labels := by
      have hz : ∀ j, raw13954step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13954step1 = (fun i j => raw13954step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13954step1 raw13954step0; decide +kernel
      have hl : raw13954step1Labels = raw13954step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13954step0 raw13954step0Labels permutation56 hz
    mixedMoment B raw13954step1 raw13954step1Labels = mixedMoment B raw13954step2 raw13954step2Labels := by
      have ha : raw13954step2 = (fun i j => raw13954step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13954step2 raw13954step1; decide +kernel
      have hl : raw13954step2Labels = raw13954step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13954step1 raw13954step1Labels permutation13 permutation7
    mixedMoment B raw13954step2 raw13954step2Labels = mixedMoment B raw13954step3 raw13954step3Labels := by
      have ha : raw13954step3 = -raw13954step2 := by apply Matrix.ext; change ∀ i j, raw13954step3 i j = -(raw13954step2 i j); unfold raw13954step3 raw13954step2; decide +kernel
      have hl : raw13954step3Labels = raw13954step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13954step3 raw13954step3Labels = mixedMoment B raw13954step4 raw13954step4Labels := by
      have ha : raw13954step4 = raw13954step3 := by apply Matrix.ext; unfold raw13954step4 raw13954step3; decide +kernel
      have hl : raw13954step3Labels = labelEmbedding1 ∘ raw13954step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13954step3 raw13954step3Labels raw13954step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

def raw13955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw13955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13955step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13955step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13955step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13955 raw13955Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw13955 raw13955Labels = mixedMoment B raw13955step0 raw13955step0Labels := by
      have hz : ∀ j, raw13955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13955step0 = (fun i j => raw13955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13955step0 raw13955; decide +kernel
      have hl : raw13955step0Labels = raw13955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13955 raw13955Labels permutation346 hz
    mixedMoment B raw13955step0 raw13955step0Labels = mixedMoment B raw13955step1 raw13955step1Labels := by
      have ha : raw13955step1 = (fun i j => raw13955step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13955step1 raw13955step0; decide +kernel
      have hl : raw13955step1Labels = raw13955step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13955step0 raw13955step0Labels permutation51 permutation7
    mixedMoment B raw13955step1 raw13955step1Labels = mixedMoment B raw13955step2 raw13955step2Labels := by
      have ha : raw13955step2 = -raw13955step1 := by apply Matrix.ext; change ∀ i j, raw13955step2 i j = -(raw13955step1 i j); unfold raw13955step2 raw13955step1; decide +kernel
      have hl : raw13955step2Labels = raw13955step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13955step2 raw13955step2Labels = mixedMoment B raw13955step3 raw13955step3Labels := by
      have ha : raw13955step3 = raw13955step2 := by apply Matrix.ext; unfold raw13955step3 raw13955step2; decide +kernel
      have hl : raw13955step2Labels = labelEmbedding1 ∘ raw13955step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13955step2 raw13955step2Labels raw13955step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw13956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw13956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13956step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13956step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13956step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13956 raw13956Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw13956 raw13956Labels = mixedMoment B raw13956step0 raw13956step0Labels := by
      have hz : ∀ j, raw13956 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13956step0 = (fun i j => raw13956 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13956step0 raw13956; decide +kernel
      have hl : raw13956step0Labels = raw13956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13956 raw13956Labels permutation265 hz
    mixedMoment B raw13956step0 raw13956step0Labels = mixedMoment B raw13956step1 raw13956step1Labels := by
      have ha : raw13956step1 = (fun i j => raw13956step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13956step1 raw13956step0; decide +kernel
      have hl : raw13956step1Labels = raw13956step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13956step0 raw13956step0Labels permutation51 permutation7
    mixedMoment B raw13956step1 raw13956step1Labels = mixedMoment B raw13956step2 raw13956step2Labels := by
      have ha : raw13956step2 = -raw13956step1 := by apply Matrix.ext; change ∀ i j, raw13956step2 i j = -(raw13956step1 i j); unfold raw13956step2 raw13956step1; decide +kernel
      have hl : raw13956step2Labels = raw13956step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13956step2 raw13956step2Labels = mixedMoment B raw13956step3 raw13956step3Labels := by
      have ha : raw13956step3 = raw13956step2 := by apply Matrix.ext; unfold raw13956step3 raw13956step2; decide +kernel
      have hl : raw13956step2Labels = labelEmbedding1 ∘ raw13956step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13956step2 raw13956step2Labels raw13956step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw13957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13957step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13957step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw13957step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13957step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13957step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13957step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13957step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13957 raw13957Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw13957 raw13957Labels = mixedMoment B raw13957step0 raw13957step0Labels := by
      have hz : ∀ j, raw13957 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13957step0 = (fun i j => raw13957 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13957step0 raw13957; decide +kernel
      have hl : raw13957step0Labels = raw13957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13957 raw13957Labels permutation346 hz
    mixedMoment B raw13957step0 raw13957step0Labels = mixedMoment B raw13957step1 raw13957step1Labels := by
      have hz : ∀ j, raw13957step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13957step1 = (fun i j => raw13957step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13957step1 raw13957step0; decide +kernel
      have hl : raw13957step1Labels = raw13957step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13957step0 raw13957step0Labels permutation56 hz
    mixedMoment B raw13957step1 raw13957step1Labels = mixedMoment B raw13957step2 raw13957step2Labels := by
      have ha : raw13957step2 = (fun i j => raw13957step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13957step2 raw13957step1; decide +kernel
      have hl : raw13957step2Labels = raw13957step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13957step1 raw13957step1Labels permutation13 permutation7
    mixedMoment B raw13957step2 raw13957step2Labels = mixedMoment B raw13957step3 raw13957step3Labels := by
      have ha : raw13957step3 = -raw13957step2 := by apply Matrix.ext; change ∀ i j, raw13957step3 i j = -(raw13957step2 i j); unfold raw13957step3 raw13957step2; decide +kernel
      have hl : raw13957step3Labels = raw13957step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13957step3 raw13957step3Labels = mixedMoment B raw13957step4 raw13957step4Labels := by
      have ha : raw13957step4 = raw13957step3 := by apply Matrix.ext; unfold raw13957step4 raw13957step3; decide +kernel
      have hl : raw13957step3Labels = labelEmbedding1 ∘ raw13957step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13957step3 raw13957step3Labels raw13957step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw13958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13958step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw13958step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13958step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13958step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13958step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13958step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13958 raw13958Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw13958 raw13958Labels = mixedMoment B raw13958step0 raw13958step0Labels := by
      have hz : ∀ j, raw13958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13958step0 = (fun i j => raw13958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13958step0 raw13958; decide +kernel
      have hl : raw13958step0Labels = raw13958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13958 raw13958Labels permutation346 hz
    mixedMoment B raw13958step0 raw13958step0Labels = mixedMoment B raw13958step1 raw13958step1Labels := by
      have hz : ∀ j, raw13958step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13958step1 = (fun i j => raw13958step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13958step1 raw13958step0; decide +kernel
      have hl : raw13958step1Labels = raw13958step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13958step0 raw13958step0Labels permutation56 hz
    mixedMoment B raw13958step1 raw13958step1Labels = mixedMoment B raw13958step2 raw13958step2Labels := by
      have ha : raw13958step2 = (fun i j => raw13958step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13958step2 raw13958step1; decide +kernel
      have hl : raw13958step2Labels = raw13958step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13958step1 raw13958step1Labels permutation13 permutation7
    mixedMoment B raw13958step2 raw13958step2Labels = mixedMoment B raw13958step3 raw13958step3Labels := by
      have ha : raw13958step3 = -raw13958step2 := by apply Matrix.ext; change ∀ i j, raw13958step3 i j = -(raw13958step2 i j); unfold raw13958step3 raw13958step2; decide +kernel
      have hl : raw13958step3Labels = raw13958step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13958step3 raw13958step3Labels = mixedMoment B raw13958step4 raw13958step4Labels := by
      have ha : raw13958step4 = raw13958step3 := by apply Matrix.ext; unfold raw13958step4 raw13958step3; decide +kernel
      have hl : raw13958step3Labels = labelEmbedding1 ∘ raw13958step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13958step3 raw13958step3Labels raw13958step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw13959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13959step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13959step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw13959step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13959step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13959step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13959step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13959step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13959 raw13959Labels = mixedMoment B node3306 node3306Labels := by
  calc
    mixedMoment B raw13959 raw13959Labels = mixedMoment B raw13959step0 raw13959step0Labels := by
      have hz : ∀ j, raw13959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13959step0 = (fun i j => raw13959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13959step0 raw13959; decide +kernel
      have hl : raw13959step0Labels = raw13959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13959 raw13959Labels permutation346 hz
    mixedMoment B raw13959step0 raw13959step0Labels = mixedMoment B raw13959step1 raw13959step1Labels := by
      have hz : ∀ j, raw13959step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13959step1 = (fun i j => raw13959step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13959step1 raw13959step0; decide +kernel
      have hl : raw13959step1Labels = raw13959step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13959step0 raw13959step0Labels permutation56 hz
    mixedMoment B raw13959step1 raw13959step1Labels = mixedMoment B raw13959step2 raw13959step2Labels := by
      have ha : raw13959step2 = (fun i j => raw13959step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13959step2 raw13959step1; decide +kernel
      have hl : raw13959step2Labels = raw13959step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13959step1 raw13959step1Labels permutation8 permutation5
    mixedMoment B raw13959step2 raw13959step2Labels = mixedMoment B raw13959step3 raw13959step3Labels := by
      have ha : raw13959step3 = -raw13959step2 := by apply Matrix.ext; change ∀ i j, raw13959step3 i j = -(raw13959step2 i j); unfold raw13959step3 raw13959step2; decide +kernel
      have hl : raw13959step3Labels = raw13959step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13959step3 raw13959step3Labels = mixedMoment B raw13959step4 raw13959step4Labels := by
      have ha : raw13959step4 = raw13959step3 := by apply Matrix.ext; unfold raw13959step4 raw13959step3; decide +kernel
      have hl : raw13959step3Labels = labelEmbedding1 ∘ raw13959step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13959step3 raw13959step3Labels raw13959step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3306 node3306Labels := by rfl

def raw13960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw13960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13960step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13960step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13960 raw13960Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw13960 raw13960Labels = mixedMoment B raw13960step0 raw13960step0Labels := by
      have hz : ∀ j, raw13960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13960step0 = (fun i j => raw13960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13960step0 raw13960; decide +kernel
      have hl : raw13960step0Labels = raw13960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13960 raw13960Labels permutation346 hz
    mixedMoment B raw13960step0 raw13960step0Labels = mixedMoment B raw13960step1 raw13960step1Labels := by
      have ha : raw13960step1 = (fun i j => raw13960step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13960step1 raw13960step0; decide +kernel
      have hl : raw13960step1Labels = raw13960step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13960step0 raw13960step0Labels permutation51 permutation7
    mixedMoment B raw13960step1 raw13960step1Labels = mixedMoment B raw13960step2 raw13960step2Labels := by
      have ha : raw13960step2 = -raw13960step1 := by apply Matrix.ext; change ∀ i j, raw13960step2 i j = -(raw13960step1 i j); unfold raw13960step2 raw13960step1; decide +kernel
      have hl : raw13960step2Labels = raw13960step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13960step2 raw13960step2Labels = mixedMoment B raw13960step3 raw13960step3Labels := by
      have ha : raw13960step3 = raw13960step2 := by apply Matrix.ext; unfold raw13960step3 raw13960step2; decide +kernel
      have hl : raw13960step2Labels = labelEmbedding1 ∘ raw13960step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13960step2 raw13960step2Labels raw13960step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw13961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw13961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13961step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13961step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13961 raw13961Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw13961 raw13961Labels = mixedMoment B raw13961step0 raw13961step0Labels := by
      have hz : ∀ j, raw13961 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13961step0 = (fun i j => raw13961 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13961step0 raw13961; decide +kernel
      have hl : raw13961step0Labels = raw13961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13961 raw13961Labels permutation265 hz
    mixedMoment B raw13961step0 raw13961step0Labels = mixedMoment B raw13961step1 raw13961step1Labels := by
      have ha : raw13961step1 = (fun i j => raw13961step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13961step1 raw13961step0; decide +kernel
      have hl : raw13961step1Labels = raw13961step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13961step0 raw13961step0Labels permutation51 permutation7
    mixedMoment B raw13961step1 raw13961step1Labels = mixedMoment B raw13961step2 raw13961step2Labels := by
      have ha : raw13961step2 = -raw13961step1 := by apply Matrix.ext; change ∀ i j, raw13961step2 i j = -(raw13961step1 i j); unfold raw13961step2 raw13961step1; decide +kernel
      have hl : raw13961step2Labels = raw13961step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13961step2 raw13961step2Labels = mixedMoment B raw13961step3 raw13961step3Labels := by
      have ha : raw13961step3 = raw13961step2 := by apply Matrix.ext; unfold raw13961step3 raw13961step2; decide +kernel
      have hl : raw13961step2Labels = labelEmbedding1 ∘ raw13961step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13961step2 raw13961step2Labels raw13961step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw13962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13962step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13962step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13962step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13962step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13962step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13962step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13962 raw13962Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw13962 raw13962Labels = mixedMoment B raw13962step0 raw13962step0Labels := by
      have hz : ∀ j, raw13962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13962step0 = (fun i j => raw13962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13962step0 raw13962; decide +kernel
      have hl : raw13962step0Labels = raw13962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13962 raw13962Labels permutation346 hz
    mixedMoment B raw13962step0 raw13962step0Labels = mixedMoment B raw13962step1 raw13962step1Labels := by
      have hz : ∀ j, raw13962step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13962step1 = (fun i j => raw13962step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13962step1 raw13962step0; decide +kernel
      have hl : raw13962step1Labels = raw13962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13962step0 raw13962step0Labels permutation56 hz
    mixedMoment B raw13962step1 raw13962step1Labels = mixedMoment B raw13962step2 raw13962step2Labels := by
      have ha : raw13962step2 = (fun i j => raw13962step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13962step2 raw13962step1; decide +kernel
      have hl : raw13962step2Labels = raw13962step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13962step1 raw13962step1Labels permutation13 permutation7
    mixedMoment B raw13962step2 raw13962step2Labels = mixedMoment B raw13962step3 raw13962step3Labels := by
      have ha : raw13962step3 = -raw13962step2 := by apply Matrix.ext; change ∀ i j, raw13962step3 i j = -(raw13962step2 i j); unfold raw13962step3 raw13962step2; decide +kernel
      have hl : raw13962step3Labels = raw13962step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13962step3 raw13962step3Labels = mixedMoment B raw13962step4 raw13962step4Labels := by
      have ha : raw13962step4 = raw13962step3 := by apply Matrix.ext; unfold raw13962step4 raw13962step3; decide +kernel
      have hl : raw13962step3Labels = labelEmbedding1 ∘ raw13962step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13962step3 raw13962step3Labels raw13962step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw13963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13963step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13963step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw13963step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13963step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13963step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13963step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13963 raw13963Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw13963 raw13963Labels = mixedMoment B raw13963step0 raw13963step0Labels := by
      have hz : ∀ j, raw13963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13963step0 = (fun i j => raw13963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13963step0 raw13963; decide +kernel
      have hl : raw13963step0Labels = raw13963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13963 raw13963Labels permutation346 hz
    mixedMoment B raw13963step0 raw13963step0Labels = mixedMoment B raw13963step1 raw13963step1Labels := by
      have hz : ∀ j, raw13963step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13963step1 = (fun i j => raw13963step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13963step1 raw13963step0; decide +kernel
      have hl : raw13963step1Labels = raw13963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13963step0 raw13963step0Labels permutation56 hz
    mixedMoment B raw13963step1 raw13963step1Labels = mixedMoment B raw13963step2 raw13963step2Labels := by
      have ha : raw13963step2 = (fun i j => raw13963step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13963step2 raw13963step1; decide +kernel
      have hl : raw13963step2Labels = raw13963step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13963step1 raw13963step1Labels permutation13 permutation7
    mixedMoment B raw13963step2 raw13963step2Labels = mixedMoment B raw13963step3 raw13963step3Labels := by
      have ha : raw13963step3 = -raw13963step2 := by apply Matrix.ext; change ∀ i j, raw13963step3 i j = -(raw13963step2 i j); unfold raw13963step3 raw13963step2; decide +kernel
      have hl : raw13963step3Labels = raw13963step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13963step3 raw13963step3Labels = mixedMoment B raw13963step4 raw13963step4Labels := by
      have ha : raw13963step4 = raw13963step3 := by apply Matrix.ext; unfold raw13963step4 raw13963step3; decide +kernel
      have hl : raw13963step3Labels = labelEmbedding1 ∘ raw13963step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13963step3 raw13963step3Labels raw13963step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw13964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13964step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13964step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13964step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw13964step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13964step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw13964step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13964 raw13964Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw13964 raw13964Labels = mixedMoment B raw13964step0 raw13964step0Labels := by
      have hz : ∀ j, raw13964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13964step0 = (fun i j => raw13964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13964step0 raw13964; decide +kernel
      have hl : raw13964step0Labels = raw13964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13964 raw13964Labels permutation346 hz
    mixedMoment B raw13964step0 raw13964step0Labels = mixedMoment B raw13964step1 raw13964step1Labels := by
      have hz : ∀ j, raw13964step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13964step1 = (fun i j => raw13964step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13964step1 raw13964step0; decide +kernel
      have hl : raw13964step1Labels = raw13964step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13964step0 raw13964step0Labels permutation56 hz
    mixedMoment B raw13964step1 raw13964step1Labels = mixedMoment B raw13964step2 raw13964step2Labels := by
      have ha : raw13964step2 = (fun i j => raw13964step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13964step2 raw13964step1; decide +kernel
      have hl : raw13964step2Labels = raw13964step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13964step1 raw13964step1Labels permutation31 permutation5
    mixedMoment B raw13964step2 raw13964step2Labels = mixedMoment B raw13964step3 raw13964step3Labels := by
      have ha : raw13964step3 = raw13964step2 := by apply Matrix.ext; unfold raw13964step3 raw13964step2; decide +kernel
      have hl : raw13964step2Labels = labelEmbedding1 ∘ raw13964step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13964step2 raw13964step2Labels raw13964step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw13965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13965step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw13965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw13965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13965 raw13965Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw13965 raw13965Labels = mixedMoment B raw13965step0 raw13965step0Labels := by
      have hz : ∀ j, raw13965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13965step0 = (fun i j => raw13965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13965step0 raw13965; decide +kernel
      have hl : raw13965step0Labels = raw13965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13965 raw13965Labels permutation346 hz
    mixedMoment B raw13965step0 raw13965step0Labels = mixedMoment B raw13965step1 raw13965step1Labels := by
      have ha : raw13965step1 = (fun i j => raw13965step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13965step1 raw13965step0; decide +kernel
      have hl : raw13965step1Labels = raw13965step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13965step0 raw13965step0Labels permutation151 permutation5
    mixedMoment B raw13965step1 raw13965step1Labels = mixedMoment B raw13965step2 raw13965step2Labels := by
      have ha : raw13965step2 = raw13965step1 := by apply Matrix.ext; unfold raw13965step2 raw13965step1; decide +kernel
      have hl : raw13965step1Labels = labelEmbedding1 ∘ raw13965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13965step1 raw13965step1Labels raw13965step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw13966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13966Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13966step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw13966step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw13966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13966 raw13966Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw13966 raw13966Labels = mixedMoment B raw13966step0 raw13966step0Labels := by
      have hz : ∀ j, raw13966 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13966step0 = (fun i j => raw13966 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13966step0 raw13966; decide +kernel
      have hl : raw13966step0Labels = raw13966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13966 raw13966Labels permutation265 hz
    mixedMoment B raw13966step0 raw13966step0Labels = mixedMoment B raw13966step1 raw13966step1Labels := by
      have ha : raw13966step1 = (fun i j => raw13966step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13966step1 raw13966step0; decide +kernel
      have hl : raw13966step1Labels = raw13966step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13966step0 raw13966step0Labels permutation151 permutation5
    mixedMoment B raw13966step1 raw13966step1Labels = mixedMoment B raw13966step2 raw13966step2Labels := by
      have ha : raw13966step2 = raw13966step1 := by apply Matrix.ext; unfold raw13966step2 raw13966step1; decide +kernel
      have hl : raw13966step1Labels = labelEmbedding1 ∘ raw13966step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13966step1 raw13966step1Labels raw13966step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw13967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13967Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13967step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13967step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw13967step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13967step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw13967step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13967 raw13967Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw13967 raw13967Labels = mixedMoment B raw13967step0 raw13967step0Labels := by
      have hz : ∀ j, raw13967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13967step0 = (fun i j => raw13967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13967step0 raw13967; decide +kernel
      have hl : raw13967step0Labels = raw13967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13967 raw13967Labels permutation346 hz
    mixedMoment B raw13967step0 raw13967step0Labels = mixedMoment B raw13967step1 raw13967step1Labels := by
      have hz : ∀ j, raw13967step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13967step1 = (fun i j => raw13967step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13967step1 raw13967step0; decide +kernel
      have hl : raw13967step1Labels = raw13967step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13967step0 raw13967step0Labels permutation56 hz
    mixedMoment B raw13967step1 raw13967step1Labels = mixedMoment B raw13967step2 raw13967step2Labels := by
      have ha : raw13967step2 = (fun i j => raw13967step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13967step2 raw13967step1; decide +kernel
      have hl : raw13967step2Labels = raw13967step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13967step1 raw13967step1Labels permutation30 permutation5
    mixedMoment B raw13967step2 raw13967step2Labels = mixedMoment B raw13967step3 raw13967step3Labels := by
      have ha : raw13967step3 = raw13967step2 := by apply Matrix.ext; unfold raw13967step3 raw13967step2; decide +kernel
      have hl : raw13967step2Labels = labelEmbedding1 ∘ raw13967step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13967step2 raw13967step2Labels raw13967step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw13968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13968Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13968step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13968step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw13968step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13968step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw13968step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13968 raw13968Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw13968 raw13968Labels = mixedMoment B raw13968step0 raw13968step0Labels := by
      have hz : ∀ j, raw13968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13968step0 = (fun i j => raw13968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13968step0 raw13968; decide +kernel
      have hl : raw13968step0Labels = raw13968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13968 raw13968Labels permutation346 hz
    mixedMoment B raw13968step0 raw13968step0Labels = mixedMoment B raw13968step1 raw13968step1Labels := by
      have hz : ∀ j, raw13968step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13968step1 = (fun i j => raw13968step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13968step1 raw13968step0; decide +kernel
      have hl : raw13968step1Labels = raw13968step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13968step0 raw13968step0Labels permutation56 hz
    mixedMoment B raw13968step1 raw13968step1Labels = mixedMoment B raw13968step2 raw13968step2Labels := by
      have ha : raw13968step2 = (fun i j => raw13968step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13968step2 raw13968step1; decide +kernel
      have hl : raw13968step2Labels = raw13968step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13968step1 raw13968step1Labels permutation29 permutation5
    mixedMoment B raw13968step2 raw13968step2Labels = mixedMoment B raw13968step3 raw13968step3Labels := by
      have ha : raw13968step3 = raw13968step2 := by apply Matrix.ext; unfold raw13968step3 raw13968step2; decide +kernel
      have hl : raw13968step2Labels = labelEmbedding1 ∘ raw13968step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13968step2 raw13968step2Labels raw13968step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw13969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13969step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13969step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13969 raw13969Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw13969 raw13969Labels = mixedMoment B raw13969step0 raw13969step0Labels := by
      have hz : ∀ j, raw13969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13969step0 = (fun i j => raw13969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13969step0 raw13969; decide +kernel
      have hl : raw13969step0Labels = raw13969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13969 raw13969Labels permutation346 hz
    mixedMoment B raw13969step0 raw13969step0Labels = mixedMoment B raw13969step1 raw13969step1Labels := by
      have ha : raw13969step1 = (fun i j => raw13969step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13969step1 raw13969step0; decide +kernel
      have hl : raw13969step1Labels = raw13969step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13969step0 raw13969step0Labels permutation37 permutation3
    mixedMoment B raw13969step1 raw13969step1Labels = mixedMoment B raw13969step2 raw13969step2Labels := by
      have ha : raw13969step2 = raw13969step1 := by apply Matrix.ext; unfold raw13969step2 raw13969step1; decide +kernel
      have hl : raw13969step1Labels = labelEmbedding6 ∘ raw13969step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13969step1 raw13969step1Labels raw13969step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw13970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13970step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13970step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13970 raw13970Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw13970 raw13970Labels = mixedMoment B raw13970step0 raw13970step0Labels := by
      have hz : ∀ j, raw13970 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13970step0 = (fun i j => raw13970 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13970step0 raw13970; decide +kernel
      have hl : raw13970step0Labels = raw13970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13970 raw13970Labels permutation265 hz
    mixedMoment B raw13970step0 raw13970step0Labels = mixedMoment B raw13970step1 raw13970step1Labels := by
      have ha : raw13970step1 = (fun i j => raw13970step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13970step1 raw13970step0; decide +kernel
      have hl : raw13970step1Labels = raw13970step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13970step0 raw13970step0Labels permutation37 permutation3
    mixedMoment B raw13970step1 raw13970step1Labels = mixedMoment B raw13970step2 raw13970step2Labels := by
      have ha : raw13970step2 = raw13970step1 := by apply Matrix.ext; unfold raw13970step2 raw13970step1; decide +kernel
      have hl : raw13970step1Labels = labelEmbedding6 ∘ raw13970step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13970step1 raw13970step1Labels raw13970step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw13971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw13971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13971step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw13971step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13971 raw13971Labels = mixedMoment B node5494 node5494Labels := by
  calc
    mixedMoment B raw13971 raw13971Labels = mixedMoment B raw13971step0 raw13971step0Labels := by
      have hz : ∀ j, raw13971 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13971step0 = (fun i j => raw13971 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13971step0 raw13971; decide +kernel
      have hl : raw13971step0Labels = raw13971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13971 raw13971Labels permutation520 hz
    mixedMoment B raw13971step0 raw13971step0Labels = mixedMoment B raw13971step1 raw13971step1Labels := by
      have hz : ∀ j, raw13971step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13971step1 = (fun i j => raw13971step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13971step1 raw13971step0; decide +kernel
      have hl : raw13971step1Labels = raw13971step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13971step0 raw13971step0Labels permutation80 hz
    mixedMoment B raw13971step1 raw13971step1Labels = mixedMoment B raw13971step2 raw13971step2Labels := by
      have hz : ∀ j, raw13971step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw13971step2 = (fun i j => raw13971step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw13971step2 raw13971step1; decide +kernel
      have hl : raw13971step2Labels = raw13971step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13971step1 raw13971step1Labels permutation14 hz
    _ = mixedMoment B node5494 node5494Labels := by rfl

def raw13972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13972step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13972step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13972step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13972step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13972 raw13972Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw13972 raw13972Labels = mixedMoment B raw13972step0 raw13972step0Labels := by
      have hz : ∀ j, raw13972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13972step0 = (fun i j => raw13972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13972step0 raw13972; decide +kernel
      have hl : raw13972step0Labels = raw13972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13972 raw13972Labels permutation346 hz
    mixedMoment B raw13972step0 raw13972step0Labels = mixedMoment B raw13972step1 raw13972step1Labels := by
      have hz : ∀ j, raw13972step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13972step1 = (fun i j => raw13972step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13972step1 raw13972step0; decide +kernel
      have hl : raw13972step1Labels = raw13972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13972step0 raw13972step0Labels permutation56 hz
    mixedMoment B raw13972step1 raw13972step1Labels = mixedMoment B raw13972step2 raw13972step2Labels := by
      have ha : raw13972step2 = (fun i j => raw13972step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13972step2 raw13972step1; decide +kernel
      have hl : raw13972step2Labels = raw13972step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13972step1 raw13972step1Labels permutation27 permutation4
    mixedMoment B raw13972step2 raw13972step2Labels = mixedMoment B raw13972step3 raw13972step3Labels := by
      have ha : raw13972step3 = -raw13972step2 := by apply Matrix.ext; change ∀ i j, raw13972step3 i j = -(raw13972step2 i j); unfold raw13972step3 raw13972step2; decide +kernel
      have hl : raw13972step3Labels = raw13972step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13972step3 raw13972step3Labels = mixedMoment B raw13972step4 raw13972step4Labels := by
      have ha : raw13972step4 = raw13972step3 := by apply Matrix.ext; unfold raw13972step4 raw13972step3; decide +kernel
      have hl : raw13972step3Labels = labelEmbedding7 ∘ raw13972step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13972step3 raw13972step3Labels raw13972step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw13973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13973step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13973step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13973 raw13973Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw13973 raw13973Labels = mixedMoment B raw13973step0 raw13973step0Labels := by
      have hz : ∀ j, raw13973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13973step0 = (fun i j => raw13973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13973step0 raw13973; decide +kernel
      have hl : raw13973step0Labels = raw13973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13973 raw13973Labels permutation346 hz
    mixedMoment B raw13973step0 raw13973step0Labels = mixedMoment B raw13973step1 raw13973step1Labels := by
      have ha : raw13973step1 = (fun i j => raw13973step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13973step1 raw13973step0; decide +kernel
      have hl : raw13973step1Labels = raw13973step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13973step0 raw13973step0Labels permutation51 permutation3
    mixedMoment B raw13973step1 raw13973step1Labels = mixedMoment B raw13973step2 raw13973step2Labels := by
      have ha : raw13973step2 = raw13973step1 := by apply Matrix.ext; unfold raw13973step2 raw13973step1; decide +kernel
      have hl : raw13973step1Labels = labelEmbedding6 ∘ raw13973step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13973step1 raw13973step1Labels raw13973step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw13974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13974step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13974 raw13974Labels = mixedMoment B node5093 node5093Labels := by
  calc
    mixedMoment B raw13974 raw13974Labels = mixedMoment B raw13974step0 raw13974step0Labels := by
      have ha : raw13974step0 = (fun i j => raw13974 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13974step0 raw13974; decide +kernel
      have hl : raw13974step0Labels = raw13974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13974 raw13974Labels permutation195 permutation3
    mixedMoment B raw13974step0 raw13974step0Labels = mixedMoment B raw13974step1 raw13974step1Labels := by
      have ha : raw13974step1 = raw13974step0 := by apply Matrix.ext; unfold raw13974step1 raw13974step0; decide +kernel
      have hl : raw13974step0Labels = labelEmbedding6 ∘ raw13974step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13974step0 raw13974step0Labels raw13974step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5093 node5093Labels := by rfl

def raw13975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw13975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13975step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13975step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13975 raw13975Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw13975 raw13975Labels = mixedMoment B raw13975step0 raw13975step0Labels := by
      have hz : ∀ j, raw13975 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13975step0 = (fun i j => raw13975 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13975step0 raw13975; decide +kernel
      have hl : raw13975step0Labels = raw13975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13975 raw13975Labels permutation520 hz
    mixedMoment B raw13975step0 raw13975step0Labels = mixedMoment B raw13975step1 raw13975step1Labels := by
      have hz : ∀ j, raw13975step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13975step1 = (fun i j => raw13975step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13975step1 raw13975step0; decide +kernel
      have hl : raw13975step1Labels = raw13975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13975step0 raw13975step0Labels permutation80 hz
    mixedMoment B raw13975step1 raw13975step1Labels = mixedMoment B raw13975step2 raw13975step2Labels := by
      have ha : raw13975step2 = (fun i j => raw13975step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13975step2 raw13975step1; decide +kernel
      have hl : raw13975step2Labels = raw13975step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13975step1 raw13975step1Labels permutation12 permutation3
    mixedMoment B raw13975step2 raw13975step2Labels = mixedMoment B raw13975step3 raw13975step3Labels := by
      have ha : raw13975step3 = raw13975step2 := by apply Matrix.ext; unfold raw13975step3 raw13975step2; decide +kernel
      have hl : raw13975step2Labels = labelEmbedding6 ∘ raw13975step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13975step2 raw13975step2Labels raw13975step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw13976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13976step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13976step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13976step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13976 raw13976Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw13976 raw13976Labels = mixedMoment B raw13976step0 raw13976step0Labels := by
      have hz : ∀ j, raw13976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13976step0 = (fun i j => raw13976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13976step0 raw13976; decide +kernel
      have hl : raw13976step0Labels = raw13976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13976 raw13976Labels permutation346 hz
    mixedMoment B raw13976step0 raw13976step0Labels = mixedMoment B raw13976step1 raw13976step1Labels := by
      have ha : raw13976step1 = (fun i j => raw13976step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13976step1 raw13976step0; decide +kernel
      have hl : raw13976step1Labels = raw13976step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13976step0 raw13976step0Labels permutation51 permutation3
    mixedMoment B raw13976step1 raw13976step1Labels = mixedMoment B raw13976step2 raw13976step2Labels := by
      have ha : raw13976step2 = raw13976step1 := by apply Matrix.ext; unfold raw13976step2 raw13976step1; decide +kernel
      have hl : raw13976step1Labels = labelEmbedding6 ∘ raw13976step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13976step1 raw13976step1Labels raw13976step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw13977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13977step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13977step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13977 raw13977Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw13977 raw13977Labels = mixedMoment B raw13977step0 raw13977step0Labels := by
      have hz : ∀ j, raw13977 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13977step0 = (fun i j => raw13977 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13977step0 raw13977; decide +kernel
      have hl : raw13977step0Labels = raw13977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13977 raw13977Labels permutation265 hz
    mixedMoment B raw13977step0 raw13977step0Labels = mixedMoment B raw13977step1 raw13977step1Labels := by
      have ha : raw13977step1 = (fun i j => raw13977step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13977step1 raw13977step0; decide +kernel
      have hl : raw13977step1Labels = raw13977step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13977step0 raw13977step0Labels permutation51 permutation3
    mixedMoment B raw13977step1 raw13977step1Labels = mixedMoment B raw13977step2 raw13977step2Labels := by
      have ha : raw13977step2 = raw13977step1 := by apply Matrix.ext; unfold raw13977step2 raw13977step1; decide +kernel
      have hl : raw13977step1Labels = labelEmbedding6 ∘ raw13977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13977step1 raw13977step1Labels raw13977step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw13978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13978step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13978 raw13978Labels = mixedMoment B node5093 node5093Labels := by
  calc
    mixedMoment B raw13978 raw13978Labels = mixedMoment B raw13978step0 raw13978step0Labels := by
      have ha : raw13978step0 = (fun i j => raw13978 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13978step0 raw13978; decide +kernel
      have hl : raw13978step0Labels = raw13978Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13978 raw13978Labels permutation171 permutation3
    mixedMoment B raw13978step0 raw13978step0Labels = mixedMoment B raw13978step1 raw13978step1Labels := by
      have ha : raw13978step1 = raw13978step0 := by apply Matrix.ext; unfold raw13978step1 raw13978step0; decide +kernel
      have hl : raw13978step0Labels = labelEmbedding6 ∘ raw13978step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13978step0 raw13978step0Labels raw13978step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5093 node5093Labels := by rfl

def raw13979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw13979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13979step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13979step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13979 raw13979Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw13979 raw13979Labels = mixedMoment B raw13979step0 raw13979step0Labels := by
      have hz : ∀ j, raw13979 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13979step0 = (fun i j => raw13979 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13979step0 raw13979; decide +kernel
      have hl : raw13979step0Labels = raw13979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13979 raw13979Labels permutation520 hz
    mixedMoment B raw13979step0 raw13979step0Labels = mixedMoment B raw13979step1 raw13979step1Labels := by
      have hz : ∀ j, raw13979step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13979step1 = (fun i j => raw13979step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13979step1 raw13979step0; decide +kernel
      have hl : raw13979step1Labels = raw13979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13979step0 raw13979step0Labels permutation56 hz
    mixedMoment B raw13979step1 raw13979step1Labels = mixedMoment B raw13979step2 raw13979step2Labels := by
      have ha : raw13979step2 = (fun i j => raw13979step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13979step2 raw13979step1; decide +kernel
      have hl : raw13979step2Labels = raw13979step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13979step1 raw13979step1Labels permutation12 permutation3
    mixedMoment B raw13979step2 raw13979step2Labels = mixedMoment B raw13979step3 raw13979step3Labels := by
      have ha : raw13979step3 = raw13979step2 := by apply Matrix.ext; unfold raw13979step3 raw13979step2; decide +kernel
      have hl : raw13979step2Labels = labelEmbedding6 ∘ raw13979step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13979step2 raw13979step2Labels raw13979step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw13980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13980step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13980step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13980 raw13980Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw13980 raw13980Labels = mixedMoment B raw13980step0 raw13980step0Labels := by
      have hz : ∀ j, raw13980 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13980step0 = (fun i j => raw13980 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13980step0 raw13980; decide +kernel
      have hl : raw13980step0Labels = raw13980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13980 raw13980Labels permutation265 hz
    mixedMoment B raw13980step0 raw13980step0Labels = mixedMoment B raw13980step1 raw13980step1Labels := by
      have ha : raw13980step1 = (fun i j => raw13980step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13980step1 raw13980step0; decide +kernel
      have hl : raw13980step1Labels = raw13980step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13980step0 raw13980step0Labels permutation51 permutation3
    mixedMoment B raw13980step1 raw13980step1Labels = mixedMoment B raw13980step2 raw13980step2Labels := by
      have ha : raw13980step2 = raw13980step1 := by apply Matrix.ext; unfold raw13980step2 raw13980step1; decide +kernel
      have hl : raw13980step1Labels = labelEmbedding6 ∘ raw13980step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13980step1 raw13980step1Labels raw13980step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw13981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13981step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13981step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13981step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13981 raw13981Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw13981 raw13981Labels = mixedMoment B raw13981step0 raw13981step0Labels := by
      have hz : ∀ j, raw13981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13981step0 = (fun i j => raw13981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13981step0 raw13981; decide +kernel
      have hl : raw13981step0Labels = raw13981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13981 raw13981Labels permutation346 hz
    mixedMoment B raw13981step0 raw13981step0Labels = mixedMoment B raw13981step1 raw13981step1Labels := by
      have hz : ∀ j, raw13981step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13981step1 = (fun i j => raw13981step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13981step1 raw13981step0; decide +kernel
      have hl : raw13981step1Labels = raw13981step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13981step0 raw13981step0Labels permutation56 hz
    mixedMoment B raw13981step1 raw13981step1Labels = mixedMoment B raw13981step2 raw13981step2Labels := by
      have ha : raw13981step2 = (fun i j => raw13981step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13981step2 raw13981step1; decide +kernel
      have hl : raw13981step2Labels = raw13981step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13981step1 raw13981step1Labels permutation13 permutation3
    mixedMoment B raw13981step2 raw13981step2Labels = mixedMoment B raw13981step3 raw13981step3Labels := by
      have ha : raw13981step3 = raw13981step2 := by apply Matrix.ext; unfold raw13981step3 raw13981step2; decide +kernel
      have hl : raw13981step2Labels = labelEmbedding6 ∘ raw13981step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13981step2 raw13981step2Labels raw13981step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw13982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13982step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13982step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13982 raw13982Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw13982 raw13982Labels = mixedMoment B raw13982step0 raw13982step0Labels := by
      have hz : ∀ j, raw13982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13982step0 = (fun i j => raw13982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13982step0 raw13982; decide +kernel
      have hl : raw13982step0Labels = raw13982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13982 raw13982Labels permutation346 hz
    mixedMoment B raw13982step0 raw13982step0Labels = mixedMoment B raw13982step1 raw13982step1Labels := by
      have ha : raw13982step1 = (fun i j => raw13982step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13982step1 raw13982step0; decide +kernel
      have hl : raw13982step1Labels = raw13982step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13982step0 raw13982step0Labels permutation37 permutation3
    mixedMoment B raw13982step1 raw13982step1Labels = mixedMoment B raw13982step2 raw13982step2Labels := by
      have ha : raw13982step2 = raw13982step1 := by apply Matrix.ext; unfold raw13982step2 raw13982step1; decide +kernel
      have hl : raw13982step1Labels = labelEmbedding6 ∘ raw13982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13982step1 raw13982step1Labels raw13982step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw13983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13983step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13983step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13983 raw13983Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw13983 raw13983Labels = mixedMoment B raw13983step0 raw13983step0Labels := by
      have hz : ∀ j, raw13983 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13983step0 = (fun i j => raw13983 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13983step0 raw13983; decide +kernel
      have hl : raw13983step0Labels = raw13983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13983 raw13983Labels permutation265 hz
    mixedMoment B raw13983step0 raw13983step0Labels = mixedMoment B raw13983step1 raw13983step1Labels := by
      have ha : raw13983step1 = (fun i j => raw13983step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13983step1 raw13983step0; decide +kernel
      have hl : raw13983step1Labels = raw13983step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13983step0 raw13983step0Labels permutation37 permutation3
    mixedMoment B raw13983step1 raw13983step1Labels = mixedMoment B raw13983step2 raw13983step2Labels := by
      have ha : raw13983step2 = raw13983step1 := by apply Matrix.ext; unfold raw13983step2 raw13983step1; decide +kernel
      have hl : raw13983step1Labels = labelEmbedding6 ∘ raw13983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13983step1 raw13983step1Labels raw13983step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw13984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw13984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw13984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13984step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw13984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13984step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -3, 1], ![1, 1, -2]]
def raw13984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13984step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw13984step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13984step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw13984step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13984 raw13984Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw13984 raw13984Labels = mixedMoment B raw13984step0 raw13984step0Labels := by
      have hz : ∀ j, raw13984 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13984step0 = (fun i j => raw13984 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13984step0 raw13984; decide +kernel
      have hl : raw13984step0Labels = raw13984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13984 raw13984Labels permutation520 hz
    mixedMoment B raw13984step0 raw13984step0Labels = mixedMoment B raw13984step1 raw13984step1Labels := by
      have hz : ∀ j, raw13984step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13984step1 = (fun i j => raw13984step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13984step1 raw13984step0; decide +kernel
      have hl : raw13984step1Labels = raw13984step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13984step0 raw13984step0Labels permutation80 hz
    mixedMoment B raw13984step1 raw13984step1Labels = mixedMoment B raw13984step2 raw13984step2Labels := by
      have hz : ∀ j, raw13984step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw13984step2 = (fun i j => raw13984step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw13984step2 raw13984step1; decide +kernel
      have hl : raw13984step2Labels = raw13984step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13984step1 raw13984step1Labels permutation14 hz
    mixedMoment B raw13984step2 raw13984step2Labels = mixedMoment B raw13984step3 raw13984step3Labels := by
      have ha : raw13984step3 = (fun i j => raw13984step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13984step3 raw13984step2; decide +kernel
      have hl : raw13984step3Labels = raw13984step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13984step2 raw13984step2Labels permutation3 permutation3
    mixedMoment B raw13984step3 raw13984step3Labels = mixedMoment B raw13984step4 raw13984step4Labels := by
      have ha : raw13984step4 = raw13984step3 := by apply Matrix.ext; unfold raw13984step4 raw13984step3; decide +kernel
      have hl : raw13984step3Labels = labelEmbedding6 ∘ raw13984step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13984step3 raw13984step3Labels raw13984step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5305 node5305Labels := by rfl

def raw13985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw13985step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw13985step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw13985step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13985 raw13985Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw13985 raw13985Labels = mixedMoment B raw13985step0 raw13985step0Labels := by
      have hz : ∀ j, raw13985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13985step0 = (fun i j => raw13985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13985step0 raw13985; decide +kernel
      have hl : raw13985step0Labels = raw13985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13985 raw13985Labels permutation346 hz
    mixedMoment B raw13985step0 raw13985step0Labels = mixedMoment B raw13985step1 raw13985step1Labels := by
      have hz : ∀ j, raw13985step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13985step1 = (fun i j => raw13985step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13985step1 raw13985step0; decide +kernel
      have hl : raw13985step1Labels = raw13985step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13985step0 raw13985step0Labels permutation56 hz
    mixedMoment B raw13985step1 raw13985step1Labels = mixedMoment B raw13985step2 raw13985step2Labels := by
      have ha : raw13985step2 = (fun i j => raw13985step1 (permutation17 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13985step2 raw13985step1; decide +kernel
      have hl : raw13985step2Labels = raw13985step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13985step1 raw13985step1Labels permutation17 permutation5
    mixedMoment B raw13985step2 raw13985step2Labels = mixedMoment B raw13985step3 raw13985step3Labels := by
      have ha : raw13985step3 = raw13985step2 := by apply Matrix.ext; unfold raw13985step3 raw13985step2; decide +kernel
      have hl : raw13985step2Labels = labelEmbedding8 ∘ raw13985step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13985step2 raw13985step2Labels raw13985step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw13986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13986step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13986step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13986step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13986 raw13986Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw13986 raw13986Labels = mixedMoment B raw13986step0 raw13986step0Labels := by
      have hz : ∀ j, raw13986 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13986step0 = (fun i j => raw13986 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13986step0 raw13986; decide +kernel
      have hl : raw13986step0Labels = raw13986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13986 raw13986Labels permutation346 hz
    mixedMoment B raw13986step0 raw13986step0Labels = mixedMoment B raw13986step1 raw13986step1Labels := by
      have hz : ∀ j, raw13986step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13986step1 = (fun i j => raw13986step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13986step1 raw13986step0; decide +kernel
      have hl : raw13986step1Labels = raw13986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13986step0 raw13986step0Labels permutation56 hz
    mixedMoment B raw13986step1 raw13986step1Labels = mixedMoment B raw13986step2 raw13986step2Labels := by
      have ha : raw13986step2 = (fun i j => raw13986step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13986step2 raw13986step1; decide +kernel
      have hl : raw13986step2Labels = raw13986step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13986step1 raw13986step1Labels permutation12 permutation3
    mixedMoment B raw13986step2 raw13986step2Labels = mixedMoment B raw13986step3 raw13986step3Labels := by
      have ha : raw13986step3 = raw13986step2 := by apply Matrix.ext; unfold raw13986step3 raw13986step2; decide +kernel
      have hl : raw13986step2Labels = labelEmbedding6 ∘ raw13986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13986step2 raw13986step2Labels raw13986step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

def raw13987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13987step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13987step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13987 raw13987Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw13987 raw13987Labels = mixedMoment B raw13987step0 raw13987step0Labels := by
      have hz : ∀ j, raw13987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13987step0 = (fun i j => raw13987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13987step0 raw13987; decide +kernel
      have hl : raw13987step0Labels = raw13987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13987 raw13987Labels permutation346 hz
    mixedMoment B raw13987step0 raw13987step0Labels = mixedMoment B raw13987step1 raw13987step1Labels := by
      have ha : raw13987step1 = (fun i j => raw13987step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13987step1 raw13987step0; decide +kernel
      have hl : raw13987step1Labels = raw13987step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13987step0 raw13987step0Labels permutation36 permutation3
    mixedMoment B raw13987step1 raw13987step1Labels = mixedMoment B raw13987step2 raw13987step2Labels := by
      have ha : raw13987step2 = raw13987step1 := by apply Matrix.ext; unfold raw13987step2 raw13987step1; decide +kernel
      have hl : raw13987step1Labels = labelEmbedding6 ∘ raw13987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13987step1 raw13987step1Labels raw13987step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw13988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13988step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13988 raw13988Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw13988 raw13988Labels = mixedMoment B raw13988step0 raw13988step0Labels := by
      have hz : ∀ j, raw13988 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13988step0 = (fun i j => raw13988 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13988step0 raw13988; decide +kernel
      have hl : raw13988step0Labels = raw13988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13988 raw13988Labels permutation265 hz
    mixedMoment B raw13988step0 raw13988step0Labels = mixedMoment B raw13988step1 raw13988step1Labels := by
      have ha : raw13988step1 = (fun i j => raw13988step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13988step1 raw13988step0; decide +kernel
      have hl : raw13988step1Labels = raw13988step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13988step0 raw13988step0Labels permutation36 permutation3
    mixedMoment B raw13988step1 raw13988step1Labels = mixedMoment B raw13988step2 raw13988step2Labels := by
      have ha : raw13988step2 = raw13988step1 := by apply Matrix.ext; unfold raw13988step2 raw13988step1; decide +kernel
      have hl : raw13988step1Labels = labelEmbedding6 ∘ raw13988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13988step1 raw13988step1Labels raw13988step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw13989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw13989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw13989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw13989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw13989step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13989step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw13989step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13989 raw13989Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw13989 raw13989Labels = mixedMoment B raw13989step0 raw13989step0Labels := by
      have hz : ∀ j, raw13989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13989step0 = (fun i j => raw13989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13989step0 raw13989; decide +kernel
      have hl : raw13989step0Labels = raw13989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13989 raw13989Labels permutation346 hz
    mixedMoment B raw13989step0 raw13989step0Labels = mixedMoment B raw13989step1 raw13989step1Labels := by
      have hz : ∀ j, raw13989step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13989step1 = (fun i j => raw13989step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13989step1 raw13989step0; decide +kernel
      have hl : raw13989step1Labels = raw13989step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13989step0 raw13989step0Labels permutation56 hz
    mixedMoment B raw13989step1 raw13989step1Labels = mixedMoment B raw13989step2 raw13989step2Labels := by
      have ha : raw13989step2 = (fun i j => raw13989step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13989step2 raw13989step1; decide +kernel
      have hl : raw13989step2Labels = raw13989step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13989step1 raw13989step1Labels permutation12 permutation3
    mixedMoment B raw13989step2 raw13989step2Labels = mixedMoment B raw13989step3 raw13989step3Labels := by
      have ha : raw13989step3 = raw13989step2 := by apply Matrix.ext; unfold raw13989step3 raw13989step2; decide +kernel
      have hl : raw13989step2Labels = labelEmbedding6 ∘ raw13989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13989step2 raw13989step2Labels raw13989step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw13990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13990step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13990step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13990step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13990 raw13990Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw13990 raw13990Labels = mixedMoment B raw13990step0 raw13990step0Labels := by
      have hz : ∀ j, raw13990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13990step0 = (fun i j => raw13990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13990step0 raw13990; decide +kernel
      have hl : raw13990step0Labels = raw13990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13990 raw13990Labels permutation346 hz
    mixedMoment B raw13990step0 raw13990step0Labels = mixedMoment B raw13990step1 raw13990step1Labels := by
      have hz : ∀ j, raw13990step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13990step1 = (fun i j => raw13990step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13990step1 raw13990step0; decide +kernel
      have hl : raw13990step1Labels = raw13990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13990step0 raw13990step0Labels permutation56 hz
    mixedMoment B raw13990step1 raw13990step1Labels = mixedMoment B raw13990step2 raw13990step2Labels := by
      have ha : raw13990step2 = (fun i j => raw13990step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13990step2 raw13990step1; decide +kernel
      have hl : raw13990step2Labels = raw13990step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13990step1 raw13990step1Labels permutation8 permutation3
    mixedMoment B raw13990step2 raw13990step2Labels = mixedMoment B raw13990step3 raw13990step3Labels := by
      have ha : raw13990step3 = raw13990step2 := by apply Matrix.ext; unfold raw13990step3 raw13990step2; decide +kernel
      have hl : raw13990step2Labels = labelEmbedding6 ∘ raw13990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13990step2 raw13990step2Labels raw13990step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw13991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13991Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13991step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13991 raw13991Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw13991 raw13991Labels = mixedMoment B raw13991step0 raw13991step0Labels := by
      have hz : ∀ j, raw13991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13991step0 = (fun i j => raw13991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13991step0 raw13991; decide +kernel
      have hl : raw13991step0Labels = raw13991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13991 raw13991Labels permutation346 hz
    mixedMoment B raw13991step0 raw13991step0Labels = mixedMoment B raw13991step1 raw13991step1Labels := by
      have ha : raw13991step1 = (fun i j => raw13991step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13991step1 raw13991step0; decide +kernel
      have hl : raw13991step1Labels = raw13991step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13991step0 raw13991step0Labels permutation37 permutation3
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw13992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13992step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13992 raw13992Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw13992 raw13992Labels = mixedMoment B raw13992step0 raw13992step0Labels := by
      have hz : ∀ j, raw13992 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13992step0 = (fun i j => raw13992 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13992step0 raw13992; decide +kernel
      have hl : raw13992step0Labels = raw13992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13992 raw13992Labels permutation265 hz
    mixedMoment B raw13992step0 raw13992step0Labels = mixedMoment B raw13992step1 raw13992step1Labels := by
      have ha : raw13992step1 = (fun i j => raw13992step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13992step1 raw13992step0; decide +kernel
      have hl : raw13992step1Labels = raw13992step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13992step0 raw13992step0Labels permutation37 permutation3
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw13993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw13993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13993step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13993step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw13993step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13993step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw13993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13993 raw13993Labels = mixedMoment B node4020 node4020Labels := by
  calc
    mixedMoment B raw13993 raw13993Labels = mixedMoment B raw13993step0 raw13993step0Labels := by
      have hz : ∀ j, raw13993 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13993step0 = (fun i j => raw13993 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13993step0 raw13993; decide +kernel
      have hl : raw13993step0Labels = raw13993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13993 raw13993Labels permutation520 hz
    mixedMoment B raw13993step0 raw13993step0Labels = mixedMoment B raw13993step1 raw13993step1Labels := by
      have hz : ∀ j, raw13993step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13993step1 = (fun i j => raw13993step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13993step1 raw13993step0; decide +kernel
      have hl : raw13993step1Labels = raw13993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13993step0 raw13993step0Labels permutation80 hz
    mixedMoment B raw13993step1 raw13993step1Labels = mixedMoment B raw13993step2 raw13993step2Labels := by
      have hz : ∀ j, raw13993step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw13993step2 = (fun i j => raw13993step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw13993step2 raw13993step1; decide +kernel
      have hl : raw13993step2Labels = raw13993step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13993step1 raw13993step1Labels permutation14 hz
    mixedMoment B raw13993step2 raw13993step2Labels = mixedMoment B raw13993step3 raw13993step3Labels := by
      have ha : raw13993step3 = (fun i j => raw13993step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13993step3 raw13993step2; decide +kernel
      have hl : raw13993step3Labels = raw13993step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13993step2 raw13993step2Labels permutation3 permutation3
    _ = mixedMoment B node4020 node4020Labels := by rfl

def raw13994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13994step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13994 raw13994Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw13994 raw13994Labels = mixedMoment B raw13994step0 raw13994step0Labels := by
      have hz : ∀ j, raw13994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13994step0 = (fun i j => raw13994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13994step0 raw13994; decide +kernel
      have hl : raw13994step0Labels = raw13994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13994 raw13994Labels permutation346 hz
    mixedMoment B raw13994step0 raw13994step0Labels = mixedMoment B raw13994step1 raw13994step1Labels := by
      have hz : ∀ j, raw13994step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13994step1 = (fun i j => raw13994step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13994step1 raw13994step0; decide +kernel
      have hl : raw13994step1Labels = raw13994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13994step0 raw13994step0Labels permutation56 hz
    mixedMoment B raw13994step1 raw13994step1Labels = mixedMoment B raw13994step2 raw13994step2Labels := by
      have ha : raw13994step2 = (fun i j => raw13994step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13994step2 raw13994step1; decide +kernel
      have hl : raw13994step2Labels = raw13994step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13994step1 raw13994step1Labels permutation30 permutation6
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw13995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13995step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13995 raw13995Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw13995 raw13995Labels = mixedMoment B raw13995step0 raw13995step0Labels := by
      have hz : ∀ j, raw13995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13995step0 = (fun i j => raw13995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13995step0 raw13995; decide +kernel
      have hl : raw13995step0Labels = raw13995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13995 raw13995Labels permutation346 hz
    mixedMoment B raw13995step0 raw13995step0Labels = mixedMoment B raw13995step1 raw13995step1Labels := by
      have ha : raw13995step1 = (fun i j => raw13995step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13995step1 raw13995step0; decide +kernel
      have hl : raw13995step1Labels = raw13995step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13995step0 raw13995step0Labels permutation51 permutation3
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw13996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13996 raw13996Labels = mixedMoment B node2503 node2503Labels := by
  calc
    mixedMoment B raw13996 raw13996Labels = mixedMoment B raw13996step0 raw13996step0Labels := by
      have ha : raw13996step0 = (fun i j => raw13996 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13996step0 raw13996; decide +kernel
      have hl : raw13996step0Labels = raw13996Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13996 raw13996Labels permutation195 permutation3
    _ = mixedMoment B node2503 node2503Labels := by rfl

def raw13997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw13997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13997step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13997step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13997 raw13997Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw13997 raw13997Labels = mixedMoment B raw13997step0 raw13997step0Labels := by
      have hz : ∀ j, raw13997 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13997step0 = (fun i j => raw13997 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13997step0 raw13997; decide +kernel
      have hl : raw13997step0Labels = raw13997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13997 raw13997Labels permutation520 hz
    mixedMoment B raw13997step0 raw13997step0Labels = mixedMoment B raw13997step1 raw13997step1Labels := by
      have hz : ∀ j, raw13997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13997step1 = (fun i j => raw13997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13997step1 raw13997step0; decide +kernel
      have hl : raw13997step1Labels = raw13997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13997step0 raw13997step0Labels permutation80 hz
    mixedMoment B raw13997step1 raw13997step1Labels = mixedMoment B raw13997step2 raw13997step2Labels := by
      have ha : raw13997step2 = (fun i j => raw13997step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13997step2 raw13997step1; decide +kernel
      have hl : raw13997step2Labels = raw13997step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13997step1 raw13997step1Labels permutation12 permutation3
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw13998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13998step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13998 raw13998Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw13998 raw13998Labels = mixedMoment B raw13998step0 raw13998step0Labels := by
      have hz : ∀ j, raw13998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13998step0 = (fun i j => raw13998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13998step0 raw13998; decide +kernel
      have hl : raw13998step0Labels = raw13998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13998 raw13998Labels permutation346 hz
    mixedMoment B raw13998step0 raw13998step0Labels = mixedMoment B raw13998step1 raw13998step1Labels := by
      have ha : raw13998step1 = (fun i j => raw13998step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13998step1 raw13998step0; decide +kernel
      have hl : raw13998step1Labels = raw13998step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13998step0 raw13998step0Labels permutation51 permutation3
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw13999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13999step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13999 raw13999Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw13999 raw13999Labels = mixedMoment B raw13999step0 raw13999step0Labels := by
      have hz : ∀ j, raw13999 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13999step0 = (fun i j => raw13999 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13999step0 raw13999; decide +kernel
      have hl : raw13999step0Labels = raw13999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13999 raw13999Labels permutation265 hz
    mixedMoment B raw13999step0 raw13999step0Labels = mixedMoment B raw13999step1 raw13999step1Labels := by
      have ha : raw13999step1 = (fun i j => raw13999step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13999step1 raw13999step0; decide +kernel
      have hl : raw13999step1Labels = raw13999step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13999step0 raw13999step0Labels permutation51 permutation3
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw14000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14000Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14000 raw14000Labels = mixedMoment B node2503 node2503Labels := by
  calc
    mixedMoment B raw14000 raw14000Labels = mixedMoment B raw14000step0 raw14000step0Labels := by
      have ha : raw14000step0 = (fun i j => raw14000 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14000step0 raw14000; decide +kernel
      have hl : raw14000step0Labels = raw14000Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14000 raw14000Labels permutation171 permutation3
    _ = mixedMoment B node2503 node2503Labels := by rfl

def raw14001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw14001Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14001step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14001step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14001 raw14001Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw14001 raw14001Labels = mixedMoment B raw14001step0 raw14001step0Labels := by
      have hz : ∀ j, raw14001 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14001step0 = (fun i j => raw14001 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14001step0 raw14001; decide +kernel
      have hl : raw14001step0Labels = raw14001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14001 raw14001Labels permutation520 hz
    mixedMoment B raw14001step0 raw14001step0Labels = mixedMoment B raw14001step1 raw14001step1Labels := by
      have hz : ∀ j, raw14001step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14001step1 = (fun i j => raw14001step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14001step1 raw14001step0; decide +kernel
      have hl : raw14001step1Labels = raw14001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14001step0 raw14001step0Labels permutation56 hz
    mixedMoment B raw14001step1 raw14001step1Labels = mixedMoment B raw14001step2 raw14001step2Labels := by
      have ha : raw14001step2 = (fun i j => raw14001step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14001step2 raw14001step1; decide +kernel
      have hl : raw14001step2Labels = raw14001step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14001step1 raw14001step1Labels permutation12 permutation3
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw14002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw14002Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw14002step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14002 raw14002Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw14002 raw14002Labels = mixedMoment B raw14002step0 raw14002step0Labels := by
      have hz : ∀ j, raw14002 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14002step0 = (fun i j => raw14002 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14002step0 raw14002; decide +kernel
      have hl : raw14002step0Labels = raw14002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14002 raw14002Labels permutation265 hz
    mixedMoment B raw14002step0 raw14002step0Labels = mixedMoment B raw14002step1 raw14002step1Labels := by
      have ha : raw14002step1 = (fun i j => raw14002step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14002step1 raw14002step0; decide +kernel
      have hl : raw14002step1Labels = raw14002step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14002step0 raw14002step0Labels permutation51 permutation3
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw14003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14003Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14003step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14003step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw14003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14003 raw14003Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw14003 raw14003Labels = mixedMoment B raw14003step0 raw14003step0Labels := by
      have hz : ∀ j, raw14003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14003step0 = (fun i j => raw14003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14003step0 raw14003; decide +kernel
      have hl : raw14003step0Labels = raw14003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14003 raw14003Labels permutation346 hz
    mixedMoment B raw14003step0 raw14003step0Labels = mixedMoment B raw14003step1 raw14003step1Labels := by
      have hz : ∀ j, raw14003step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14003step1 = (fun i j => raw14003step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14003step1 raw14003step0; decide +kernel
      have hl : raw14003step1Labels = raw14003step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14003step0 raw14003step0Labels permutation56 hz
    mixedMoment B raw14003step1 raw14003step1Labels = mixedMoment B raw14003step2 raw14003step2Labels := by
      have ha : raw14003step2 = (fun i j => raw14003step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14003step2 raw14003step1; decide +kernel
      have hl : raw14003step2Labels = raw14003step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14003step1 raw14003step1Labels permutation13 permutation3
    _ = mixedMoment B node1074 node1074Labels := by rfl

def raw14004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14004Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14004step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw14004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14004 raw14004Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw14004 raw14004Labels = mixedMoment B raw14004step0 raw14004step0Labels := by
      have hz : ∀ j, raw14004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14004step0 = (fun i j => raw14004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14004step0 raw14004; decide +kernel
      have hl : raw14004step0Labels = raw14004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14004 raw14004Labels permutation346 hz
    mixedMoment B raw14004step0 raw14004step0Labels = mixedMoment B raw14004step1 raw14004step1Labels := by
      have ha : raw14004step1 = (fun i j => raw14004step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14004step1 raw14004step0; decide +kernel
      have hl : raw14004step1Labels = raw14004step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14004step0 raw14004step0Labels permutation37 permutation3
    _ = mixedMoment B node2504 node2504Labels := by rfl

def raw14005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14005Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14005step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw14005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14005 raw14005Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw14005 raw14005Labels = mixedMoment B raw14005step0 raw14005step0Labels := by
      have hz : ∀ j, raw14005 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14005step0 = (fun i j => raw14005 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14005step0 raw14005; decide +kernel
      have hl : raw14005step0Labels = raw14005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14005 raw14005Labels permutation265 hz
    mixedMoment B raw14005step0 raw14005step0Labels = mixedMoment B raw14005step1 raw14005step1Labels := by
      have ha : raw14005step1 = (fun i j => raw14005step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14005step1 raw14005step0; decide +kernel
      have hl : raw14005step1Labels = raw14005step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14005step0 raw14005step0Labels permutation37 permutation3
    _ = mixedMoment B node2504 node2504Labels := by rfl

def raw14006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw14006Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw14006step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw14006step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14006step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -3, 1], ![1, 1, -2]]
def raw14006step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14006step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw14006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14006 raw14006Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw14006 raw14006Labels = mixedMoment B raw14006step0 raw14006step0Labels := by
      have hz : ∀ j, raw14006 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14006step0 = (fun i j => raw14006 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14006step0 raw14006; decide +kernel
      have hl : raw14006step0Labels = raw14006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14006 raw14006Labels permutation520 hz
    mixedMoment B raw14006step0 raw14006step0Labels = mixedMoment B raw14006step1 raw14006step1Labels := by
      have hz : ∀ j, raw14006step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14006step1 = (fun i j => raw14006step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14006step1 raw14006step0; decide +kernel
      have hl : raw14006step1Labels = raw14006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14006step0 raw14006step0Labels permutation80 hz
    mixedMoment B raw14006step1 raw14006step1Labels = mixedMoment B raw14006step2 raw14006step2Labels := by
      have hz : ∀ j, raw14006step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw14006step2 = (fun i j => raw14006step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw14006step2 raw14006step1; decide +kernel
      have hl : raw14006step2Labels = raw14006step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14006step1 raw14006step1Labels permutation14 hz
    mixedMoment B raw14006step2 raw14006step2Labels = mixedMoment B raw14006step3 raw14006step3Labels := by
      have ha : raw14006step3 = (fun i j => raw14006step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14006step3 raw14006step2; decide +kernel
      have hl : raw14006step3Labels = raw14006step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14006step2 raw14006step2Labels permutation3 permutation3
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw14007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw14007Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw14007step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw14007step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw14007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14007 raw14007Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw14007 raw14007Labels = mixedMoment B raw14007step0 raw14007step0Labels := by
      have hz : ∀ j, raw14007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14007step0 = (fun i j => raw14007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14007step0 raw14007; decide +kernel
      have hl : raw14007step0Labels = raw14007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14007 raw14007Labels permutation346 hz
    mixedMoment B raw14007step0 raw14007step0Labels = mixedMoment B raw14007step1 raw14007step1Labels := by
      have hz : ∀ j, raw14007step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14007step1 = (fun i j => raw14007step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14007step1 raw14007step0; decide +kernel
      have hl : raw14007step1Labels = raw14007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14007step0 raw14007step0Labels permutation56 hz
    mixedMoment B raw14007step1 raw14007step1Labels = mixedMoment B raw14007step2 raw14007step2Labels := by
      have ha : raw14007step2 = (fun i j => raw14007step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14007step2 raw14007step1; decide +kernel
      have hl : raw14007step2Labels = raw14007step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14007step1 raw14007step1Labels permutation13 permutation3
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw14008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14008Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14008step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14008step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14008step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14008 raw14008Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw14008 raw14008Labels = mixedMoment B raw14008step0 raw14008step0Labels := by
      have hz : ∀ j, raw14008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14008step0 = (fun i j => raw14008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14008step0 raw14008; decide +kernel
      have hl : raw14008step0Labels = raw14008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14008 raw14008Labels permutation346 hz
    mixedMoment B raw14008step0 raw14008step0Labels = mixedMoment B raw14008step1 raw14008step1Labels := by
      have hz : ∀ j, raw14008step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14008step1 = (fun i j => raw14008step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14008step1 raw14008step0; decide +kernel
      have hl : raw14008step1Labels = raw14008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14008step0 raw14008step0Labels permutation56 hz
    mixedMoment B raw14008step1 raw14008step1Labels = mixedMoment B raw14008step2 raw14008step2Labels := by
      have ha : raw14008step2 = (fun i j => raw14008step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14008step2 raw14008step1; decide +kernel
      have hl : raw14008step2Labels = raw14008step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14008step1 raw14008step1Labels permutation12 permutation3
    _ = mixedMoment B node1075 node1075Labels := by rfl

def raw14009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14009Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14009step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14009 raw14009Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw14009 raw14009Labels = mixedMoment B raw14009step0 raw14009step0Labels := by
      have hz : ∀ j, raw14009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14009step0 = (fun i j => raw14009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14009step0 raw14009; decide +kernel
      have hl : raw14009step0Labels = raw14009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14009 raw14009Labels permutation346 hz
    mixedMoment B raw14009step0 raw14009step0Labels = mixedMoment B raw14009step1 raw14009step1Labels := by
      have ha : raw14009step1 = (fun i j => raw14009step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14009step1 raw14009step0; decide +kernel
      have hl : raw14009step1Labels = raw14009step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14009step0 raw14009step0Labels permutation36 permutation3
    _ = mixedMoment B node2505 node2505Labels := by rfl

def raw14010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14010Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14010step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14010 raw14010Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw14010 raw14010Labels = mixedMoment B raw14010step0 raw14010step0Labels := by
      have hz : ∀ j, raw14010 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14010step0 = (fun i j => raw14010 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14010step0 raw14010; decide +kernel
      have hl : raw14010step0Labels = raw14010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14010 raw14010Labels permutation265 hz
    mixedMoment B raw14010step0 raw14010step0Labels = mixedMoment B raw14010step1 raw14010step1Labels := by
      have ha : raw14010step1 = (fun i j => raw14010step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14010step1 raw14010step0; decide +kernel
      have hl : raw14010step1Labels = raw14010step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14010step0 raw14010step0Labels permutation36 permutation3
    _ = mixedMoment B node2505 node2505Labels := by rfl

def raw14011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw14011Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw14011step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw14011step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw14011step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14011 raw14011Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw14011 raw14011Labels = mixedMoment B raw14011step0 raw14011step0Labels := by
      have hz : ∀ j, raw14011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14011step0 = (fun i j => raw14011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14011step0 raw14011; decide +kernel
      have hl : raw14011step0Labels = raw14011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14011 raw14011Labels permutation346 hz
    mixedMoment B raw14011step0 raw14011step0Labels = mixedMoment B raw14011step1 raw14011step1Labels := by
      have hz : ∀ j, raw14011step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14011step1 = (fun i j => raw14011step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14011step1 raw14011step0; decide +kernel
      have hl : raw14011step1Labels = raw14011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14011step0 raw14011step0Labels permutation56 hz
    mixedMoment B raw14011step1 raw14011step1Labels = mixedMoment B raw14011step2 raw14011step2Labels := by
      have ha : raw14011step2 = (fun i j => raw14011step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14011step2 raw14011step1; decide +kernel
      have hl : raw14011step2Labels = raw14011step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14011step1 raw14011step1Labels permutation12 permutation3
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw14012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14012Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14012step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14012step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14012 raw14012Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw14012 raw14012Labels = mixedMoment B raw14012step0 raw14012step0Labels := by
      have hz : ∀ j, raw14012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14012step0 = (fun i j => raw14012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14012step0 raw14012; decide +kernel
      have hl : raw14012step0Labels = raw14012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14012 raw14012Labels permutation346 hz
    mixedMoment B raw14012step0 raw14012step0Labels = mixedMoment B raw14012step1 raw14012step1Labels := by
      have hz : ∀ j, raw14012step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14012step1 = (fun i j => raw14012step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14012step1 raw14012step0; decide +kernel
      have hl : raw14012step1Labels = raw14012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14012step0 raw14012step0Labels permutation56 hz
    mixedMoment B raw14012step1 raw14012step1Labels = mixedMoment B raw14012step2 raw14012step2Labels := by
      have ha : raw14012step2 = (fun i j => raw14012step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14012step2 raw14012step1; decide +kernel
      have hl : raw14012step2Labels = raw14012step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14012step1 raw14012step1Labels permutation8 permutation3
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw14013 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14013step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14013step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14013 raw14013Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw14013 raw14013Labels = mixedMoment B raw14013step0 raw14013step0Labels := by
      have hz : ∀ j, raw14013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14013step0 = (fun i j => raw14013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14013step0 raw14013; decide +kernel
      have hl : raw14013step0Labels = raw14013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14013 raw14013Labels permutation346 hz
    mixedMoment B raw14013step0 raw14013step0Labels = mixedMoment B raw14013step1 raw14013step1Labels := by
      have ha : raw14013step1 = (fun i j => raw14013step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14013step1 raw14013step0; decide +kernel
      have hl : raw14013step1Labels = raw14013step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14013step0 raw14013step0Labels permutation32 permutation7
    mixedMoment B raw14013step1 raw14013step1Labels = mixedMoment B raw14013step2 raw14013step2Labels := by
      have ha : raw14013step2 = raw14013step1 := by apply Matrix.ext; unfold raw14013step2 raw14013step1; decide +kernel
      have hl : raw14013step1Labels = labelEmbedding10 ∘ raw14013step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14013step1 raw14013step1Labels raw14013step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw14014 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14014step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14014step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14014 raw14014Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw14014 raw14014Labels = mixedMoment B raw14014step0 raw14014step0Labels := by
      have hz : ∀ j, raw14014 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14014step0 = (fun i j => raw14014 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14014step0 raw14014; decide +kernel
      have hl : raw14014step0Labels = raw14014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14014 raw14014Labels permutation265 hz
    mixedMoment B raw14014step0 raw14014step0Labels = mixedMoment B raw14014step1 raw14014step1Labels := by
      have ha : raw14014step1 = (fun i j => raw14014step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14014step1 raw14014step0; decide +kernel
      have hl : raw14014step1Labels = raw14014step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14014step0 raw14014step0Labels permutation32 permutation7
    mixedMoment B raw14014step1 raw14014step1Labels = mixedMoment B raw14014step2 raw14014step2Labels := by
      have ha : raw14014step2 = raw14014step1 := by apply Matrix.ext; unfold raw14014step2 raw14014step1; decide +kernel
      have hl : raw14014step1Labels = labelEmbedding10 ∘ raw14014step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14014step1 raw14014step1Labels raw14014step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw14015 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14015step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14015step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14015step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14015 raw14015Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw14015 raw14015Labels = mixedMoment B raw14015step0 raw14015step0Labels := by
      have hz : ∀ j, raw14015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14015step0 = (fun i j => raw14015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14015step0 raw14015; decide +kernel
      have hl : raw14015step0Labels = raw14015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14015 raw14015Labels permutation346 hz
    mixedMoment B raw14015step0 raw14015step0Labels = mixedMoment B raw14015step1 raw14015step1Labels := by
      have hz : ∀ j, raw14015step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14015step1 = (fun i j => raw14015step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14015step1 raw14015step0; decide +kernel
      have hl : raw14015step1Labels = raw14015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14015step0 raw14015step0Labels permutation56 hz
    mixedMoment B raw14015step1 raw14015step1Labels = mixedMoment B raw14015step2 raw14015step2Labels := by
      have ha : raw14015step2 = (fun i j => raw14015step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14015step2 raw14015step1; decide +kernel
      have hl : raw14015step2Labels = raw14015step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14015step1 raw14015step1Labels permutation8 permutation7
    mixedMoment B raw14015step2 raw14015step2Labels = mixedMoment B raw14015step3 raw14015step3Labels := by
      have ha : raw14015step3 = raw14015step2 := by apply Matrix.ext; unfold raw14015step3 raw14015step2; decide +kernel
      have hl : raw14015step2Labels = labelEmbedding10 ∘ raw14015step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14015step2 raw14015step2Labels raw14015step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw14016 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14016step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14016step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14016 raw14016Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw14016 raw14016Labels = mixedMoment B raw14016step0 raw14016step0Labels := by
      have hz : ∀ j, raw14016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14016step0 = (fun i j => raw14016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14016step0 raw14016; decide +kernel
      have hl : raw14016step0Labels = raw14016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14016 raw14016Labels permutation346 hz
    mixedMoment B raw14016step0 raw14016step0Labels = mixedMoment B raw14016step1 raw14016step1Labels := by
      have hz : ∀ j, raw14016step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14016step1 = (fun i j => raw14016step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14016step1 raw14016step0; decide +kernel
      have hl : raw14016step1Labels = raw14016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14016step0 raw14016step0Labels permutation56 hz
    mixedMoment B raw14016step1 raw14016step1Labels = mixedMoment B raw14016step2 raw14016step2Labels := by
      have ha : raw14016step2 = (fun i j => raw14016step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14016step2 raw14016step1; decide +kernel
      have hl : raw14016step2Labels = raw14016step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14016step1 raw14016step1Labels permutation31 permutation3
    mixedMoment B raw14016step2 raw14016step2Labels = mixedMoment B raw14016step3 raw14016step3Labels := by
      have ha : raw14016step3 = raw14016step2 := by apply Matrix.ext; unfold raw14016step3 raw14016step2; decide +kernel
      have hl : raw14016step2Labels = labelEmbedding6 ∘ raw14016step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14016step2 raw14016step2Labels raw14016step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw14017 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14017step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14017step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14017step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14017 raw14017Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw14017 raw14017Labels = mixedMoment B raw14017step0 raw14017step0Labels := by
      have hz : ∀ j, raw14017 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14017step0 = (fun i j => raw14017 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14017step0 raw14017; decide +kernel
      have hl : raw14017step0Labels = raw14017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14017 raw14017Labels permutation265 hz
    mixedMoment B raw14017step0 raw14017step0Labels = mixedMoment B raw14017step1 raw14017step1Labels := by
      have ha : raw14017step1 = (fun i j => raw14017step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14017step1 raw14017step0; decide +kernel
      have hl : raw14017step1Labels = raw14017step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14017step0 raw14017step0Labels permutation51 permutation4
    mixedMoment B raw14017step1 raw14017step1Labels = mixedMoment B raw14017step2 raw14017step2Labels := by
      have ha : raw14017step2 = -raw14017step1 := by apply Matrix.ext; change ∀ i j, raw14017step2 i j = -(raw14017step1 i j); unfold raw14017step2 raw14017step1; decide +kernel
      have hl : raw14017step2Labels = raw14017step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14017step2 raw14017step2Labels = mixedMoment B raw14017step3 raw14017step3Labels := by
      have ha : raw14017step3 = raw14017step2 := by apply Matrix.ext; unfold raw14017step3 raw14017step2; decide +kernel
      have hl : raw14017step2Labels = labelEmbedding7 ∘ raw14017step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14017step2 raw14017step2Labels raw14017step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw14018 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14018step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14018step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14018 raw14018Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw14018 raw14018Labels = mixedMoment B raw14018step0 raw14018step0Labels := by
      have ha : raw14018step0 = (fun i j => raw14018 (permutation157 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14018step0 raw14018; decide +kernel
      have hl : raw14018step0Labels = raw14018Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14018 raw14018Labels permutation157 permutation6
    mixedMoment B raw14018step0 raw14018step0Labels = mixedMoment B raw14018step1 raw14018step1Labels := by
      have ha : raw14018step1 = raw14018step0 := by apply Matrix.ext; unfold raw14018step1 raw14018step0; decide +kernel
      have hl : raw14018step0Labels = labelEmbedding9 ∘ raw14018step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14018step0 raw14018step0Labels raw14018step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw14019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14019step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14019step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14019 raw14019Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw14019 raw14019Labels = mixedMoment B raw14019step0 raw14019step0Labels := by
      have hz : ∀ j, raw14019 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14019step0 = (fun i j => raw14019 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14019step0 raw14019; decide +kernel
      have hl : raw14019step0Labels = raw14019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14019 raw14019Labels permutation265 hz
    mixedMoment B raw14019step0 raw14019step0Labels = mixedMoment B raw14019step1 raw14019step1Labels := by
      have ha : raw14019step1 = (fun i j => raw14019step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14019step1 raw14019step0; decide +kernel
      have hl : raw14019step1Labels = raw14019step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14019step0 raw14019step0Labels permutation37 permutation6
    mixedMoment B raw14019step1 raw14019step1Labels = mixedMoment B raw14019step2 raw14019step2Labels := by
      have ha : raw14019step2 = raw14019step1 := by apply Matrix.ext; unfold raw14019step2 raw14019step1; decide +kernel
      have hl : raw14019step1Labels = labelEmbedding9 ∘ raw14019step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14019step1 raw14019step1Labels raw14019step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw14020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw14020step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw14020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14020 raw14020Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw14020 raw14020Labels = mixedMoment B raw14020step0 raw14020step0Labels := by
      have hz : ∀ j, raw14020 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14020step0 = (fun i j => raw14020 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14020step0 raw14020; decide +kernel
      have hl : raw14020step0Labels = raw14020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14020 raw14020Labels permutation265 hz
    mixedMoment B raw14020step0 raw14020step0Labels = mixedMoment B raw14020step1 raw14020step1Labels := by
      have ha : raw14020step1 = (fun i j => raw14020step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14020step1 raw14020step0; decide +kernel
      have hl : raw14020step1Labels = raw14020step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14020step0 raw14020step0Labels permutation146 permutation3
    mixedMoment B raw14020step1 raw14020step1Labels = mixedMoment B raw14020step2 raw14020step2Labels := by
      have ha : raw14020step2 = raw14020step1 := by apply Matrix.ext; unfold raw14020step2 raw14020step1; decide +kernel
      have hl : raw14020step1Labels = labelEmbedding6 ∘ raw14020step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14020step1 raw14020step1Labels raw14020step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

def raw14021 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14021step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw14021step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14021step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw14021step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14021step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw14021step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14021 raw14021Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw14021 raw14021Labels = mixedMoment B raw14021step0 raw14021step0Labels := by
      have hz : ∀ j, raw14021 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14021step0 = (fun i j => raw14021 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14021step0 raw14021; decide +kernel
      have hl : raw14021step0Labels = raw14021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14021 raw14021Labels permutation346 hz
    mixedMoment B raw14021step0 raw14021step0Labels = mixedMoment B raw14021step1 raw14021step1Labels := by
      have hz : ∀ j, raw14021step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14021step1 = (fun i j => raw14021step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14021step1 raw14021step0; decide +kernel
      have hl : raw14021step1Labels = raw14021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14021step0 raw14021step0Labels permutation56 hz
    mixedMoment B raw14021step1 raw14021step1Labels = mixedMoment B raw14021step2 raw14021step2Labels := by
      have ha : raw14021step2 = (fun i j => raw14021step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14021step2 raw14021step1; decide +kernel
      have hl : raw14021step2Labels = raw14021step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14021step1 raw14021step1Labels permutation13 permutation4
    mixedMoment B raw14021step2 raw14021step2Labels = mixedMoment B raw14021step3 raw14021step3Labels := by
      have ha : raw14021step3 = -raw14021step2 := by apply Matrix.ext; change ∀ i j, raw14021step3 i j = -(raw14021step2 i j); unfold raw14021step3 raw14021step2; decide +kernel
      have hl : raw14021step3Labels = raw14021step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14021step3 raw14021step3Labels = mixedMoment B raw14021step4 raw14021step4Labels := by
      have ha : raw14021step4 = raw14021step3 := by apply Matrix.ext; unfold raw14021step4 raw14021step3; decide +kernel
      have hl : raw14021step3Labels = labelEmbedding7 ∘ raw14021step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14021step3 raw14021step3Labels raw14021step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw14022 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14022step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14022 raw14022Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw14022 raw14022Labels = mixedMoment B raw14022step0 raw14022step0Labels := by
      have hz : ∀ j, raw14022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14022step0 = (fun i j => raw14022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14022step0 raw14022; decide +kernel
      have hl : raw14022step0Labels = raw14022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14022 raw14022Labels permutation346 hz
    mixedMoment B raw14022step0 raw14022step0Labels = mixedMoment B raw14022step1 raw14022step1Labels := by
      have ha : raw14022step1 = (fun i j => raw14022step0 (permutation95 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14022step1 raw14022step0; decide +kernel
      have hl : raw14022step1Labels = raw14022step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14022step0 raw14022step0Labels permutation95 permutation5
    mixedMoment B raw14022step1 raw14022step1Labels = mixedMoment B raw14022step2 raw14022step2Labels := by
      have ha : raw14022step2 = raw14022step1 := by apply Matrix.ext; unfold raw14022step2 raw14022step1; decide +kernel
      have hl : raw14022step1Labels = labelEmbedding8 ∘ raw14022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14022step1 raw14022step1Labels raw14022step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw14023 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14023step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14023step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14023 raw14023Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw14023 raw14023Labels = mixedMoment B raw14023step0 raw14023step0Labels := by
      have hz : ∀ j, raw14023 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14023step0 = (fun i j => raw14023 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14023step0 raw14023; decide +kernel
      have hl : raw14023step0Labels = raw14023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14023 raw14023Labels permutation265 hz
    mixedMoment B raw14023step0 raw14023step0Labels = mixedMoment B raw14023step1 raw14023step1Labels := by
      have ha : raw14023step1 = (fun i j => raw14023step0 (permutation95 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14023step1 raw14023step0; decide +kernel
      have hl : raw14023step1Labels = raw14023step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14023step0 raw14023step0Labels permutation95 permutation5
    mixedMoment B raw14023step1 raw14023step1Labels = mixedMoment B raw14023step2 raw14023step2Labels := by
      have ha : raw14023step2 = raw14023step1 := by apply Matrix.ext; unfold raw14023step2 raw14023step1; decide +kernel
      have hl : raw14023step1Labels = labelEmbedding8 ∘ raw14023step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14023step1 raw14023step1Labels raw14023step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw14024 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14024step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14024step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14024step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14024step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14024 raw14024Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw14024 raw14024Labels = mixedMoment B raw14024step0 raw14024step0Labels := by
      have hz : ∀ j, raw14024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14024step0 = (fun i j => raw14024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14024step0 raw14024; decide +kernel
      have hl : raw14024step0Labels = raw14024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14024 raw14024Labels permutation346 hz
    mixedMoment B raw14024step0 raw14024step0Labels = mixedMoment B raw14024step1 raw14024step1Labels := by
      have hz : ∀ j, raw14024step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14024step1 = (fun i j => raw14024step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14024step1 raw14024step0; decide +kernel
      have hl : raw14024step1Labels = raw14024step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14024step0 raw14024step0Labels permutation56 hz
    mixedMoment B raw14024step1 raw14024step1Labels = mixedMoment B raw14024step2 raw14024step2Labels := by
      have ha : raw14024step2 = (fun i j => raw14024step1 (permutation17 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14024step2 raw14024step1; decide +kernel
      have hl : raw14024step2Labels = raw14024step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14024step1 raw14024step1Labels permutation17 permutation5
    mixedMoment B raw14024step2 raw14024step2Labels = mixedMoment B raw14024step3 raw14024step3Labels := by
      have ha : raw14024step3 = raw14024step2 := by apply Matrix.ext; unfold raw14024step3 raw14024step2; decide +kernel
      have hl : raw14024step2Labels = labelEmbedding8 ∘ raw14024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14024step2 raw14024step2Labels raw14024step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw14025 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14025step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw14025step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14025step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw14025step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14025 raw14025Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw14025 raw14025Labels = mixedMoment B raw14025step0 raw14025step0Labels := by
      have hz : ∀ j, raw14025 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14025step0 = (fun i j => raw14025 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14025step0 raw14025; decide +kernel
      have hl : raw14025step0Labels = raw14025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14025 raw14025Labels permutation346 hz
    mixedMoment B raw14025step0 raw14025step0Labels = mixedMoment B raw14025step1 raw14025step1Labels := by
      have hz : ∀ j, raw14025step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14025step1 = (fun i j => raw14025step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14025step1 raw14025step0; decide +kernel
      have hl : raw14025step1Labels = raw14025step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14025step0 raw14025step0Labels permutation56 hz
    mixedMoment B raw14025step1 raw14025step1Labels = mixedMoment B raw14025step2 raw14025step2Labels := by
      have ha : raw14025step2 = (fun i j => raw14025step1 (permutation16 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14025step2 raw14025step1; decide +kernel
      have hl : raw14025step2Labels = raw14025step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14025step1 raw14025step1Labels permutation16 permutation5
    mixedMoment B raw14025step2 raw14025step2Labels = mixedMoment B raw14025step3 raw14025step3Labels := by
      have ha : raw14025step3 = raw14025step2 := by apply Matrix.ext; unfold raw14025step3 raw14025step2; decide +kernel
      have hl : raw14025step2Labels = labelEmbedding8 ∘ raw14025step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14025step2 raw14025step2Labels raw14025step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw14026 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw14026step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14026step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw14026step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14026step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw14026step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14026 raw14026Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw14026 raw14026Labels = mixedMoment B raw14026step0 raw14026step0Labels := by
      have hz : ∀ j, raw14026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14026step0 = (fun i j => raw14026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14026step0 raw14026; decide +kernel
      have hl : raw14026step0Labels = raw14026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14026 raw14026Labels permutation346 hz
    mixedMoment B raw14026step0 raw14026step0Labels = mixedMoment B raw14026step1 raw14026step1Labels := by
      have hz : ∀ j, raw14026step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14026step1 = (fun i j => raw14026step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14026step1 raw14026step0; decide +kernel
      have hl : raw14026step1Labels = raw14026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14026step0 raw14026step0Labels permutation56 hz
    mixedMoment B raw14026step1 raw14026step1Labels = mixedMoment B raw14026step2 raw14026step2Labels := by
      have ha : raw14026step2 = (fun i j => raw14026step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14026step2 raw14026step1; decide +kernel
      have hl : raw14026step2Labels = raw14026step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14026step1 raw14026step1Labels permutation12 permutation4
    mixedMoment B raw14026step2 raw14026step2Labels = mixedMoment B raw14026step3 raw14026step3Labels := by
      have ha : raw14026step3 = -raw14026step2 := by apply Matrix.ext; change ∀ i j, raw14026step3 i j = -(raw14026step2 i j); unfold raw14026step3 raw14026step2; decide +kernel
      have hl : raw14026step3Labels = raw14026step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14026step3 raw14026step3Labels = mixedMoment B raw14026step4 raw14026step4Labels := by
      have ha : raw14026step4 = raw14026step3 := by apply Matrix.ext; unfold raw14026step4 raw14026step3; decide +kernel
      have hl : raw14026step3Labels = labelEmbedding7 ∘ raw14026step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14026step3 raw14026step3Labels raw14026step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4875 node4875Labels := by rfl

def raw14027 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14027step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14027 raw14027Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw14027 raw14027Labels = mixedMoment B raw14027step0 raw14027step0Labels := by
      have hz : ∀ j, raw14027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14027step0 = (fun i j => raw14027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14027step0 raw14027; decide +kernel
      have hl : raw14027step0Labels = raw14027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14027 raw14027Labels permutation346 hz
    mixedMoment B raw14027step0 raw14027step0Labels = mixedMoment B raw14027step1 raw14027step1Labels := by
      have ha : raw14027step1 = (fun i j => raw14027step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14027step1 raw14027step0; decide +kernel
      have hl : raw14027step1Labels = raw14027step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14027step0 raw14027step0Labels permutation36 permutation6
    mixedMoment B raw14027step1 raw14027step1Labels = mixedMoment B raw14027step2 raw14027step2Labels := by
      have ha : raw14027step2 = raw14027step1 := by apply Matrix.ext; unfold raw14027step2 raw14027step1; decide +kernel
      have hl : raw14027step1Labels = labelEmbedding9 ∘ raw14027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14027step1 raw14027step1Labels raw14027step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw14028 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14028step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14028 raw14028Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw14028 raw14028Labels = mixedMoment B raw14028step0 raw14028step0Labels := by
      have hz : ∀ j, raw14028 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14028step0 = (fun i j => raw14028 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14028step0 raw14028; decide +kernel
      have hl : raw14028step0Labels = raw14028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14028 raw14028Labels permutation265 hz
    mixedMoment B raw14028step0 raw14028step0Labels = mixedMoment B raw14028step1 raw14028step1Labels := by
      have ha : raw14028step1 = (fun i j => raw14028step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14028step1 raw14028step0; decide +kernel
      have hl : raw14028step1Labels = raw14028step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14028step0 raw14028step0Labels permutation36 permutation6
    mixedMoment B raw14028step1 raw14028step1Labels = mixedMoment B raw14028step2 raw14028step2Labels := by
      have ha : raw14028step2 = raw14028step1 := by apply Matrix.ext; unfold raw14028step2 raw14028step1; decide +kernel
      have hl : raw14028step1Labels = labelEmbedding9 ∘ raw14028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14028step1 raw14028step1Labels raw14028step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw14029 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw14029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw14029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw14029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw14029step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14029step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw14029step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14029 raw14029Labels = mixedMoment B node5303 node5303Labels := by
  calc
    mixedMoment B raw14029 raw14029Labels = mixedMoment B raw14029step0 raw14029step0Labels := by
      have hz : ∀ j, raw14029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14029step0 = (fun i j => raw14029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14029step0 raw14029; decide +kernel
      have hl : raw14029step0Labels = raw14029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14029 raw14029Labels permutation346 hz
    mixedMoment B raw14029step0 raw14029step0Labels = mixedMoment B raw14029step1 raw14029step1Labels := by
      have hz : ∀ j, raw14029step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14029step1 = (fun i j => raw14029step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14029step1 raw14029step0; decide +kernel
      have hl : raw14029step1Labels = raw14029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14029step0 raw14029step0Labels permutation56 hz
    mixedMoment B raw14029step1 raw14029step1Labels = mixedMoment B raw14029step2 raw14029step2Labels := by
      have ha : raw14029step2 = (fun i j => raw14029step1 (permutation26 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14029step2 raw14029step1; decide +kernel
      have hl : raw14029step2Labels = raw14029step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14029step1 raw14029step1Labels permutation26 permutation3
    mixedMoment B raw14029step2 raw14029step2Labels = mixedMoment B raw14029step3 raw14029step3Labels := by
      have ha : raw14029step3 = raw14029step2 := by apply Matrix.ext; unfold raw14029step3 raw14029step2; decide +kernel
      have hl : raw14029step2Labels = labelEmbedding6 ∘ raw14029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14029step2 raw14029step2Labels raw14029step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5303 node5303Labels := by rfl

def raw14030 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14030step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14030step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14030step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14030step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14030step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14030step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14030step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14030 raw14030Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw14030 raw14030Labels = mixedMoment B raw14030step0 raw14030step0Labels := by
      have hz : ∀ j, raw14030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14030step0 = (fun i j => raw14030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14030step0 raw14030; decide +kernel
      have hl : raw14030step0Labels = raw14030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14030 raw14030Labels permutation346 hz
    mixedMoment B raw14030step0 raw14030step0Labels = mixedMoment B raw14030step1 raw14030step1Labels := by
      have hz : ∀ j, raw14030step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14030step1 = (fun i j => raw14030step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14030step1 raw14030step0; decide +kernel
      have hl : raw14030step1Labels = raw14030step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14030step0 raw14030step0Labels permutation56 hz
    mixedMoment B raw14030step1 raw14030step1Labels = mixedMoment B raw14030step2 raw14030step2Labels := by
      have ha : raw14030step2 = (fun i j => raw14030step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14030step2 raw14030step1; decide +kernel
      have hl : raw14030step2Labels = raw14030step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14030step1 raw14030step1Labels permutation13 permutation4
    mixedMoment B raw14030step2 raw14030step2Labels = mixedMoment B raw14030step3 raw14030step3Labels := by
      have ha : raw14030step3 = -raw14030step2 := by apply Matrix.ext; change ∀ i j, raw14030step3 i j = -(raw14030step2 i j); unfold raw14030step3 raw14030step2; decide +kernel
      have hl : raw14030step3Labels = raw14030step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14030step3 raw14030step3Labels = mixedMoment B raw14030step4 raw14030step4Labels := by
      have ha : raw14030step4 = raw14030step3 := by apply Matrix.ext; unfold raw14030step4 raw14030step3; decide +kernel
      have hl : raw14030step3Labels = labelEmbedding7 ∘ raw14030step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14030step3 raw14030step3Labels raw14030step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw14031 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14031step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14031 raw14031Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw14031 raw14031Labels = mixedMoment B raw14031step0 raw14031step0Labels := by
      have hz : ∀ j, raw14031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14031step0 = (fun i j => raw14031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14031step0 raw14031; decide +kernel
      have hl : raw14031step0Labels = raw14031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14031 raw14031Labels permutation346 hz
    mixedMoment B raw14031step0 raw14031step0Labels = mixedMoment B raw14031step1 raw14031step1Labels := by
      have ha : raw14031step1 = (fun i j => raw14031step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14031step1 raw14031step0; decide +kernel
      have hl : raw14031step1Labels = raw14031step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14031step0 raw14031step0Labels permutation37 permutation6
    mixedMoment B raw14031step1 raw14031step1Labels = mixedMoment B raw14031step2 raw14031step2Labels := by
      have ha : raw14031step2 = raw14031step1 := by apply Matrix.ext; unfold raw14031step2 raw14031step1; decide +kernel
      have hl : raw14031step1Labels = labelEmbedding9 ∘ raw14031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14031step1 raw14031step1Labels raw14031step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw14032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14032step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14032step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14032step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14032 raw14032Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw14032 raw14032Labels = mixedMoment B raw14032step0 raw14032step0Labels := by
      have hz : ∀ j, raw14032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14032step0 = (fun i j => raw14032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14032step0 raw14032; decide +kernel
      have hl : raw14032step0Labels = raw14032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14032 raw14032Labels permutation346 hz
    mixedMoment B raw14032step0 raw14032step0Labels = mixedMoment B raw14032step1 raw14032step1Labels := by
      have hz : ∀ j, raw14032step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14032step1 = (fun i j => raw14032step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14032step1 raw14032step0; decide +kernel
      have hl : raw14032step1Labels = raw14032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14032step0 raw14032step0Labels permutation56 hz
    mixedMoment B raw14032step1 raw14032step1Labels = mixedMoment B raw14032step2 raw14032step2Labels := by
      have ha : raw14032step2 = (fun i j => raw14032step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14032step2 raw14032step1; decide +kernel
      have hl : raw14032step2Labels = raw14032step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14032step1 raw14032step1Labels permutation11 permutation6
    mixedMoment B raw14032step2 raw14032step2Labels = mixedMoment B raw14032step3 raw14032step3Labels := by
      have ha : raw14032step3 = raw14032step2 := by apply Matrix.ext; unfold raw14032step3 raw14032step2; decide +kernel
      have hl : raw14032step2Labels = labelEmbedding9 ∘ raw14032step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14032step2 raw14032step2Labels raw14032step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw14033 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14033step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14033 raw14033Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw14033 raw14033Labels = mixedMoment B raw14033step0 raw14033step0Labels := by
      have hz : ∀ j, raw14033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14033step0 = (fun i j => raw14033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14033step0 raw14033; decide +kernel
      have hl : raw14033step0Labels = raw14033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14033 raw14033Labels permutation346 hz
    mixedMoment B raw14033step0 raw14033step0Labels = mixedMoment B raw14033step1 raw14033step1Labels := by
      have ha : raw14033step1 = (fun i j => raw14033step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14033step1 raw14033step0; decide +kernel
      have hl : raw14033step1Labels = raw14033step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14033step0 raw14033step0Labels permutation37 permutation6
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw14034 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14034step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14034 raw14034Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw14034 raw14034Labels = mixedMoment B raw14034step0 raw14034step0Labels := by
      have hz : ∀ j, raw14034 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14034step0 = (fun i j => raw14034 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14034step0 raw14034; decide +kernel
      have hl : raw14034step0Labels = raw14034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14034 raw14034Labels permutation265 hz
    mixedMoment B raw14034step0 raw14034step0Labels = mixedMoment B raw14034step1 raw14034step1Labels := by
      have ha : raw14034step1 = (fun i j => raw14034step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14034step1 raw14034step0; decide +kernel
      have hl : raw14034step1Labels = raw14034step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14034step0 raw14034step0Labels permutation37 permutation6
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw14035 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14035step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14035step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14035step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14035 raw14035Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw14035 raw14035Labels = mixedMoment B raw14035step0 raw14035step0Labels := by
      have hz : ∀ j, raw14035 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14035step0 = (fun i j => raw14035 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14035step0 raw14035; decide +kernel
      have hl : raw14035step0Labels = raw14035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14035 raw14035Labels permutation346 hz
    mixedMoment B raw14035step0 raw14035step0Labels = mixedMoment B raw14035step1 raw14035step1Labels := by
      have hz : ∀ j, raw14035step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14035step1 = (fun i j => raw14035step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14035step1 raw14035step0; decide +kernel
      have hl : raw14035step1Labels = raw14035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14035step0 raw14035step0Labels permutation56 hz
    mixedMoment B raw14035step1 raw14035step1Labels = mixedMoment B raw14035step2 raw14035step2Labels := by
      have ha : raw14035step2 = (fun i j => raw14035step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14035step2 raw14035step1; decide +kernel
      have hl : raw14035step2Labels = raw14035step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14035step1 raw14035step1Labels permutation13 permutation6
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw14036 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14036step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14036step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14036 raw14036Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw14036 raw14036Labels = mixedMoment B raw14036step0 raw14036step0Labels := by
      have hz : ∀ j, raw14036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14036step0 = (fun i j => raw14036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14036step0 raw14036; decide +kernel
      have hl : raw14036step0Labels = raw14036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14036 raw14036Labels permutation346 hz
    mixedMoment B raw14036step0 raw14036step0Labels = mixedMoment B raw14036step1 raw14036step1Labels := by
      have hz : ∀ j, raw14036step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14036step1 = (fun i j => raw14036step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14036step1 raw14036step0; decide +kernel
      have hl : raw14036step1Labels = raw14036step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14036step0 raw14036step0Labels permutation56 hz
    mixedMoment B raw14036step1 raw14036step1Labels = mixedMoment B raw14036step2 raw14036step2Labels := by
      have ha : raw14036step2 = (fun i j => raw14036step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14036step2 raw14036step1; decide +kernel
      have hl : raw14036step2Labels = raw14036step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14036step1 raw14036step1Labels permutation31 permutation3
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw14037 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14037step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14037 raw14037Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw14037 raw14037Labels = mixedMoment B raw14037step0 raw14037step0Labels := by
      have hz : ∀ j, raw14037 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14037step0 = (fun i j => raw14037 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14037step0 raw14037; decide +kernel
      have hl : raw14037step0Labels = raw14037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14037 raw14037Labels permutation265 hz
    mixedMoment B raw14037step0 raw14037step0Labels = mixedMoment B raw14037step1 raw14037step1Labels := by
      have ha : raw14037step1 = (fun i j => raw14037step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14037step1 raw14037step0; decide +kernel
      have hl : raw14037step1Labels = raw14037step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14037step0 raw14037step0Labels permutation37 permutation6
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw14038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14038 raw14038Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw14038 raw14038Labels = mixedMoment B raw14038step0 raw14038step0Labels := by
      have ha : raw14038step0 = (fun i j => raw14038 (permutation157 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14038step0 raw14038; decide +kernel
      have hl : raw14038step0Labels = raw14038Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14038 raw14038Labels permutation157 permutation6
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw14039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14039step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14039 raw14039Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw14039 raw14039Labels = mixedMoment B raw14039step0 raw14039step0Labels := by
      have hz : ∀ j, raw14039 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14039step0 = (fun i j => raw14039 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14039step0 raw14039; decide +kernel
      have hl : raw14039step0Labels = raw14039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14039 raw14039Labels permutation265 hz
    mixedMoment B raw14039step0 raw14039step0Labels = mixedMoment B raw14039step1 raw14039step1Labels := by
      have ha : raw14039step1 = (fun i j => raw14039step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14039step1 raw14039step0; decide +kernel
      have hl : raw14039step1Labels = raw14039step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14039step0 raw14039step0Labels permutation37 permutation6
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw14040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14040step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw14040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14040 raw14040Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw14040 raw14040Labels = mixedMoment B raw14040step0 raw14040step0Labels := by
      have hz : ∀ j, raw14040 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14040step0 = (fun i j => raw14040 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14040step0 raw14040; decide +kernel
      have hl : raw14040step0Labels = raw14040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14040 raw14040Labels permutation265 hz
    mixedMoment B raw14040step0 raw14040step0Labels = mixedMoment B raw14040step1 raw14040step1Labels := by
      have ha : raw14040step1 = (fun i j => raw14040step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14040step1 raw14040step0; decide +kernel
      have hl : raw14040step1Labels = raw14040step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14040step0 raw14040step0Labels permutation146 permutation3
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw14041 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14041step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14041step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw14041step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14041 raw14041Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw14041 raw14041Labels = mixedMoment B raw14041step0 raw14041step0Labels := by
      have hz : ∀ j, raw14041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14041step0 = (fun i j => raw14041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14041step0 raw14041; decide +kernel
      have hl : raw14041step0Labels = raw14041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14041 raw14041Labels permutation346 hz
    mixedMoment B raw14041step0 raw14041step0Labels = mixedMoment B raw14041step1 raw14041step1Labels := by
      have hz : ∀ j, raw14041step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14041step1 = (fun i j => raw14041step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14041step1 raw14041step0; decide +kernel
      have hl : raw14041step1Labels = raw14041step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14041step0 raw14041step0Labels permutation56 hz
    mixedMoment B raw14041step1 raw14041step1Labels = mixedMoment B raw14041step2 raw14041step2Labels := by
      have ha : raw14041step2 = (fun i j => raw14041step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14041step2 raw14041step1; decide +kernel
      have hl : raw14041step2Labels = raw14041step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14041step1 raw14041step1Labels permutation13 permutation6
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw14042 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw14042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14042 raw14042Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw14042 raw14042Labels = mixedMoment B raw14042step0 raw14042step0Labels := by
      have hz : ∀ j, raw14042 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14042step0 = (fun i j => raw14042 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14042step0 raw14042; decide +kernel
      have hl : raw14042step0Labels = raw14042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14042 raw14042Labels permutation346 hz
    mixedMoment B raw14042step0 raw14042step0Labels = mixedMoment B raw14042step1 raw14042step1Labels := by
      have ha : raw14042step1 = (fun i j => raw14042step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14042step1 raw14042step0; decide +kernel
      have hl : raw14042step1Labels = raw14042step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14042step0 raw14042step0Labels permutation37 permutation6
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw14043 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw14043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14043 raw14043Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw14043 raw14043Labels = mixedMoment B raw14043step0 raw14043step0Labels := by
      have hz : ∀ j, raw14043 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14043step0 = (fun i j => raw14043 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14043step0 raw14043; decide +kernel
      have hl : raw14043step0Labels = raw14043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14043 raw14043Labels permutation265 hz
    mixedMoment B raw14043step0 raw14043step0Labels = mixedMoment B raw14043step1 raw14043step1Labels := by
      have ha : raw14043step1 = (fun i j => raw14043step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14043step1 raw14043step0; decide +kernel
      have hl : raw14043step1Labels = raw14043step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14043step0 raw14043step0Labels permutation37 permutation6
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw14044 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14044step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14044step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14044step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw14044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14044 raw14044Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw14044 raw14044Labels = mixedMoment B raw14044step0 raw14044step0Labels := by
      have hz : ∀ j, raw14044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14044step0 = (fun i j => raw14044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14044step0 raw14044; decide +kernel
      have hl : raw14044step0Labels = raw14044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14044 raw14044Labels permutation346 hz
    mixedMoment B raw14044step0 raw14044step0Labels = mixedMoment B raw14044step1 raw14044step1Labels := by
      have hz : ∀ j, raw14044step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14044step1 = (fun i j => raw14044step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14044step1 raw14044step0; decide +kernel
      have hl : raw14044step1Labels = raw14044step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14044step0 raw14044step0Labels permutation56 hz
    mixedMoment B raw14044step1 raw14044step1Labels = mixedMoment B raw14044step2 raw14044step2Labels := by
      have ha : raw14044step2 = (fun i j => raw14044step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14044step2 raw14044step1; decide +kernel
      have hl : raw14044step2Labels = raw14044step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14044step1 raw14044step1Labels permutation13 permutation6
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw14045 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14045step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14045step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14045step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw14045step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14045 raw14045Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw14045 raw14045Labels = mixedMoment B raw14045step0 raw14045step0Labels := by
      have hz : ∀ j, raw14045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14045step0 = (fun i j => raw14045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14045step0 raw14045; decide +kernel
      have hl : raw14045step0Labels = raw14045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14045 raw14045Labels permutation346 hz
    mixedMoment B raw14045step0 raw14045step0Labels = mixedMoment B raw14045step1 raw14045step1Labels := by
      have hz : ∀ j, raw14045step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14045step1 = (fun i j => raw14045step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14045step1 raw14045step0; decide +kernel
      have hl : raw14045step1Labels = raw14045step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14045step0 raw14045step0Labels permutation56 hz
    mixedMoment B raw14045step1 raw14045step1Labels = mixedMoment B raw14045step2 raw14045step2Labels := by
      have ha : raw14045step2 = (fun i j => raw14045step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14045step2 raw14045step1; decide +kernel
      have hl : raw14045step2Labels = raw14045step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14045step1 raw14045step1Labels permutation30 permutation3
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw14046 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14046step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14046step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14046 raw14046Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw14046 raw14046Labels = mixedMoment B raw14046step0 raw14046step0Labels := by
      have hz : ∀ j, raw14046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14046step0 = (fun i j => raw14046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14046step0 raw14046; decide +kernel
      have hl : raw14046step0Labels = raw14046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14046 raw14046Labels permutation346 hz
    mixedMoment B raw14046step0 raw14046step0Labels = mixedMoment B raw14046step1 raw14046step1Labels := by
      have hz : ∀ j, raw14046step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14046step1 = (fun i j => raw14046step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14046step1 raw14046step0; decide +kernel
      have hl : raw14046step1Labels = raw14046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14046step0 raw14046step0Labels permutation56 hz
    mixedMoment B raw14046step1 raw14046step1Labels = mixedMoment B raw14046step2 raw14046step2Labels := by
      have ha : raw14046step2 = (fun i j => raw14046step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14046step2 raw14046step1; decide +kernel
      have hl : raw14046step2Labels = raw14046step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14046step1 raw14046step1Labels permutation12 permutation6
    _ = mixedMoment B node2288 node2288Labels := by rfl

def raw14047 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14047 raw14047Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw14047 raw14047Labels = mixedMoment B raw14047step0 raw14047step0Labels := by
      have hz : ∀ j, raw14047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14047step0 = (fun i j => raw14047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14047step0 raw14047; decide +kernel
      have hl : raw14047step0Labels = raw14047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14047 raw14047Labels permutation346 hz
    mixedMoment B raw14047step0 raw14047step0Labels = mixedMoment B raw14047step1 raw14047step1Labels := by
      have ha : raw14047step1 = (fun i j => raw14047step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14047step1 raw14047step0; decide +kernel
      have hl : raw14047step1Labels = raw14047step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14047step0 raw14047step0Labels permutation36 permutation6
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw14048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14048step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14048 raw14048Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw14048 raw14048Labels = mixedMoment B raw14048step0 raw14048step0Labels := by
      have hz : ∀ j, raw14048 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14048step0 = (fun i j => raw14048 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14048step0 raw14048; decide +kernel
      have hl : raw14048step0Labels = raw14048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14048 raw14048Labels permutation265 hz
    mixedMoment B raw14048step0 raw14048step0Labels = mixedMoment B raw14048step1 raw14048step1Labels := by
      have ha : raw14048step1 = (fun i j => raw14048step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14048step1 raw14048step0; decide +kernel
      have hl : raw14048step1Labels = raw14048step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14048step0 raw14048step0Labels permutation36 permutation6
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw14049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw14049Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw14049step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw14049step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw14049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14049 raw14049Labels = mixedMoment B node2779 node2779Labels := by
  calc
    mixedMoment B raw14049 raw14049Labels = mixedMoment B raw14049step0 raw14049step0Labels := by
      have hz : ∀ j, raw14049 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14049step0 = (fun i j => raw14049 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14049step0 raw14049; decide +kernel
      have hl : raw14049step0Labels = raw14049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14049 raw14049Labels permutation346 hz
    mixedMoment B raw14049step0 raw14049step0Labels = mixedMoment B raw14049step1 raw14049step1Labels := by
      have hz : ∀ j, raw14049step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14049step1 = (fun i j => raw14049step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14049step1 raw14049step0; decide +kernel
      have hl : raw14049step1Labels = raw14049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14049step0 raw14049step0Labels permutation56 hz
    mixedMoment B raw14049step1 raw14049step1Labels = mixedMoment B raw14049step2 raw14049step2Labels := by
      have ha : raw14049step2 = (fun i j => raw14049step1 (permutation26 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14049step2 raw14049step1; decide +kernel
      have hl : raw14049step2Labels = raw14049step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14049step1 raw14049step1Labels permutation26 permutation3
    _ = mixedMoment B node2779 node2779Labels := by rfl

def raw14050 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14050step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14050 raw14050Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw14050 raw14050Labels = mixedMoment B raw14050step0 raw14050step0Labels := by
      have hz : ∀ j, raw14050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14050step0 = (fun i j => raw14050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14050step0 raw14050; decide +kernel
      have hl : raw14050step0Labels = raw14050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14050 raw14050Labels permutation346 hz
    mixedMoment B raw14050step0 raw14050step0Labels = mixedMoment B raw14050step1 raw14050step1Labels := by
      have hz : ∀ j, raw14050step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14050step1 = (fun i j => raw14050step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14050step1 raw14050step0; decide +kernel
      have hl : raw14050step1Labels = raw14050step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14050step0 raw14050step0Labels permutation56 hz
    mixedMoment B raw14050step1 raw14050step1Labels = mixedMoment B raw14050step2 raw14050step2Labels := by
      have ha : raw14050step2 = (fun i j => raw14050step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14050step2 raw14050step1; decide +kernel
      have hl : raw14050step2Labels = raw14050step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14050step1 raw14050step1Labels permutation13 permutation6
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw14051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14051 raw14051Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw14051 raw14051Labels = mixedMoment B raw14051step0 raw14051step0Labels := by
      have hz : ∀ j, raw14051 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14051step0 = (fun i j => raw14051 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14051step0 raw14051; decide +kernel
      have hl : raw14051step0Labels = raw14051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14051 raw14051Labels permutation346 hz
    mixedMoment B raw14051step0 raw14051step0Labels = mixedMoment B raw14051step1 raw14051step1Labels := by
      have ha : raw14051step1 = (fun i j => raw14051step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14051step1 raw14051step0; decide +kernel
      have hl : raw14051step1Labels = raw14051step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14051step0 raw14051step0Labels permutation37 permutation6
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw14052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14052step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14052 raw14052Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw14052 raw14052Labels = mixedMoment B raw14052step0 raw14052step0Labels := by
      have hz : ∀ j, raw14052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14052step0 = (fun i j => raw14052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14052step0 raw14052; decide +kernel
      have hl : raw14052step0Labels = raw14052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14052 raw14052Labels permutation346 hz
    mixedMoment B raw14052step0 raw14052step0Labels = mixedMoment B raw14052step1 raw14052step1Labels := by
      have hz : ∀ j, raw14052step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14052step1 = (fun i j => raw14052step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14052step1 raw14052step0; decide +kernel
      have hl : raw14052step1Labels = raw14052step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14052step0 raw14052step0Labels permutation56 hz
    mixedMoment B raw14052step1 raw14052step1Labels = mixedMoment B raw14052step2 raw14052step2Labels := by
      have ha : raw14052step2 = (fun i j => raw14052step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14052step2 raw14052step1; decide +kernel
      have hl : raw14052step2Labels = raw14052step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14052step1 raw14052step1Labels permutation11 permutation6
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw14053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14053 raw14053Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw14053 raw14053Labels = mixedMoment B raw14053step0 raw14053step0Labels := by
      have hz : ∀ j, raw14053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14053step0 = (fun i j => raw14053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14053step0 raw14053; decide +kernel
      have hl : raw14053step0Labels = raw14053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14053 raw14053Labels permutation346 hz
    mixedMoment B raw14053step0 raw14053step0Labels = mixedMoment B raw14053step1 raw14053step1Labels := by
      have ha : raw14053step1 = (fun i j => raw14053step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14053step1 raw14053step0; decide +kernel
      have hl : raw14053step1Labels = raw14053step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14053step0 raw14053step0Labels permutation36 permutation2
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw14054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14054 raw14054Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw14054 raw14054Labels = mixedMoment B raw14054step0 raw14054step0Labels := by
      have hz : ∀ j, raw14054 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14054step0 = (fun i j => raw14054 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14054step0 raw14054; decide +kernel
      have hl : raw14054step0Labels = raw14054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14054 raw14054Labels permutation265 hz
    mixedMoment B raw14054step0 raw14054step0Labels = mixedMoment B raw14054step1 raw14054step1Labels := by
      have ha : raw14054step1 = (fun i j => raw14054step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14054step1 raw14054step0; decide +kernel
      have hl : raw14054step1Labels = raw14054step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14054step0 raw14054step0Labels permutation36 permutation2
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw14055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14055step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]
def raw14055step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14055step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw14055step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw14055step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw14055step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14055 raw14055Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw14055 raw14055Labels = mixedMoment B raw14055step0 raw14055step0Labels := by
      have hz : ∀ j, raw14055 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14055step0 = (fun i j => raw14055 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14055step0 raw14055; decide +kernel
      have hl : raw14055step0Labels = raw14055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14055 raw14055Labels permutation590 hz
    mixedMoment B raw14055step0 raw14055step0Labels = mixedMoment B raw14055step1 raw14055step1Labels := by
      have hz : ∀ j, raw14055step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14055step1 = (fun i j => raw14055step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14055step1 raw14055step0; decide +kernel
      have hl : raw14055step1Labels = raw14055step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14055step0 raw14055step0Labels permutation80 hz
    mixedMoment B raw14055step1 raw14055step1Labels = mixedMoment B raw14055step2 raw14055step2Labels := by
      have hz : ∀ j, raw14055step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw14055step2 = (fun i j => raw14055step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw14055step2 raw14055step1; decide +kernel
      have hl : raw14055step2Labels = raw14055step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14055step1 raw14055step1Labels permutation14 hz
    mixedMoment B raw14055step2 raw14055step2Labels = mixedMoment B raw14055step3 raw14055step3Labels := by
      have hz : ∀ i, raw14055step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw14055step3 = (fun i j => raw14055step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw14055step3 raw14055step2; decide +kernel
      have hl : raw14055step3Labels = (fun j => raw14055step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14055step2 raw14055step2Labels permutation4 hz
    mixedMoment B raw14055step3 raw14055step3Labels = mixedMoment B raw14055step4 raw14055step4Labels := by
      have ha : raw14055step4 = raw14055step3 := by apply Matrix.ext; unfold raw14055step4 raw14055step3; decide +kernel
      have hl : raw14055step3Labels = labelEmbedding2 ∘ raw14055step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14055step3 raw14055step3Labels raw14055step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw14056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14056step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14056 raw14056Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw14056 raw14056Labels = mixedMoment B raw14056step0 raw14056step0Labels := by
      have hz : ∀ j, raw14056 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14056step0 = (fun i j => raw14056 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14056step0 raw14056; decide +kernel
      have hl : raw14056step0Labels = raw14056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14056 raw14056Labels permutation346 hz
    mixedMoment B raw14056step0 raw14056step0Labels = mixedMoment B raw14056step1 raw14056step1Labels := by
      have ha : raw14056step1 = (fun i j => raw14056step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14056step1 raw14056step0; decide +kernel
      have hl : raw14056step1Labels = raw14056step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14056step0 raw14056step0Labels permutation36 permutation2
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw14057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14057 raw14057Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw14057 raw14057Labels = mixedMoment B raw14057step0 raw14057step0Labels := by
      have ha : raw14057step0 = (fun i j => raw14057 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14057step0 raw14057; decide +kernel
      have hl : raw14057step0Labels = raw14057Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14057 raw14057Labels permutation180 permutation2
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw14058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14058 raw14058Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14058 raw14058Labels = mixedMoment B raw14058step0 raw14058step0Labels := by
      have hz : ∀ j, raw14058 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14058step0 = (fun i j => raw14058 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14058step0 raw14058; decide +kernel
      have hl : raw14058step0Labels = raw14058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14058 raw14058Labels permutation346 hz
    mixedMoment B raw14058step0 raw14058step0Labels = mixedMoment B raw14058step1 raw14058step1Labels := by
      have ha : raw14058step1 = (fun i j => raw14058step0 (permutation45 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14058step1 raw14058step0; decide +kernel
      have hl : raw14058step1Labels = raw14058step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14058step0 raw14058step0Labels permutation45 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw14059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14059step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14059 raw14059Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw14059 raw14059Labels = mixedMoment B raw14059step0 raw14059step0Labels := by
      have hz : ∀ j, raw14059 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14059step0 = (fun i j => raw14059 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14059step0 raw14059; decide +kernel
      have hl : raw14059step0Labels = raw14059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14059 raw14059Labels permutation590 hz
    mixedMoment B raw14059step0 raw14059step0Labels = mixedMoment B raw14059step1 raw14059step1Labels := by
      have hz : ∀ j, raw14059step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14059step1 = (fun i j => raw14059step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14059step1 raw14059step0; decide +kernel
      have hl : raw14059step1Labels = raw14059step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14059step0 raw14059step0Labels permutation80 hz
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw14060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14060step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14060step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14060 raw14060Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw14060 raw14060Labels = mixedMoment B raw14060step0 raw14060step0Labels := by
      have hz : ∀ j, raw14060 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14060step0 = (fun i j => raw14060 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14060step0 raw14060; decide +kernel
      have hl : raw14060step0Labels = raw14060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14060 raw14060Labels permutation265 hz
    mixedMoment B raw14060step0 raw14060step0Labels = mixedMoment B raw14060step1 raw14060step1Labels := by
      have ha : raw14060step1 = (fun i j => raw14060step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14060step1 raw14060step0; decide +kernel
      have hl : raw14060step1Labels = raw14060step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14060step0 raw14060step0Labels permutation36 permutation2
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw14061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14061 raw14061Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw14061 raw14061Labels = mixedMoment B raw14061step0 raw14061step0Labels := by
      have ha : raw14061step0 = (fun i j => raw14061 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14061step0 raw14061; decide +kernel
      have hl : raw14061step0Labels = raw14061Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14061 raw14061Labels permutation156 permutation2
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw14062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14062step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14062 raw14062Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14062 raw14062Labels = mixedMoment B raw14062step0 raw14062step0Labels := by
      have hz : ∀ j, raw14062 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14062step0 = (fun i j => raw14062 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14062step0 raw14062; decide +kernel
      have hl : raw14062step0Labels = raw14062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14062 raw14062Labels permutation265 hz
    mixedMoment B raw14062step0 raw14062step0Labels = mixedMoment B raw14062step1 raw14062step1Labels := by
      have ha : raw14062step1 = (fun i j => raw14062step0 (permutation45 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14062step1 raw14062step0; decide +kernel
      have hl : raw14062step1Labels = raw14062step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14062step0 raw14062step0Labels permutation45 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw14063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14063 raw14063Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw14063 raw14063Labels = mixedMoment B raw14063step0 raw14063step0Labels := by
      have hz : ∀ j, raw14063 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14063step0 = (fun i j => raw14063 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14063step0 raw14063; decide +kernel
      have hl : raw14063step0Labels = raw14063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14063 raw14063Labels permutation590 hz
    mixedMoment B raw14063step0 raw14063step0Labels = mixedMoment B raw14063step1 raw14063step1Labels := by
      have hz : ∀ j, raw14063step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14063step1 = (fun i j => raw14063step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14063step1 raw14063step0; decide +kernel
      have hl : raw14063step1Labels = raw14063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14063step0 raw14063step0Labels permutation56 hz
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw14064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14064step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14064 raw14064Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw14064 raw14064Labels = mixedMoment B raw14064step0 raw14064step0Labels := by
      have hz : ∀ j, raw14064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14064step0 = (fun i j => raw14064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14064step0 raw14064; decide +kernel
      have hl : raw14064step0Labels = raw14064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14064 raw14064Labels permutation346 hz
    mixedMoment B raw14064step0 raw14064step0Labels = mixedMoment B raw14064step1 raw14064step1Labels := by
      have hz : ∀ j, raw14064step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14064step1 = (fun i j => raw14064step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14064step1 raw14064step0; decide +kernel
      have hl : raw14064step1Labels = raw14064step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14064step0 raw14064step0Labels permutation56 hz
    mixedMoment B raw14064step1 raw14064step1Labels = mixedMoment B raw14064step2 raw14064step2Labels := by
      have ha : raw14064step2 = (fun i j => raw14064step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14064step2 raw14064step1; decide +kernel
      have hl : raw14064step2Labels = raw14064step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14064step1 raw14064step1Labels permutation13 permutation2
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw14065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14065 raw14065Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw14065 raw14065Labels = mixedMoment B raw14065step0 raw14065step0Labels := by
      have hz : ∀ j, raw14065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14065step0 = (fun i j => raw14065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14065step0 raw14065; decide +kernel
      have hl : raw14065step0Labels = raw14065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14065 raw14065Labels permutation346 hz
    mixedMoment B raw14065step0 raw14065step0Labels = mixedMoment B raw14065step1 raw14065step1Labels := by
      have ha : raw14065step1 = (fun i j => raw14065step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14065step1 raw14065step0; decide +kernel
      have hl : raw14065step1Labels = raw14065step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14065step0 raw14065step0Labels permutation37 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw14066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14066step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14066 raw14066Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw14066 raw14066Labels = mixedMoment B raw14066step0 raw14066step0Labels := by
      have hz : ∀ j, raw14066 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14066step0 = (fun i j => raw14066 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14066step0 raw14066; decide +kernel
      have hl : raw14066step0Labels = raw14066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14066 raw14066Labels permutation265 hz
    mixedMoment B raw14066step0 raw14066step0Labels = mixedMoment B raw14066step1 raw14066step1Labels := by
      have ha : raw14066step1 = (fun i j => raw14066step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14066step1 raw14066step0; decide +kernel
      have hl : raw14066step1Labels = raw14066step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14066step0 raw14066step0Labels permutation37 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw14067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14067step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14067 raw14067Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw14067 raw14067Labels = mixedMoment B raw14067step0 raw14067step0Labels := by
      have hz : ∀ j, raw14067 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14067step0 = (fun i j => raw14067 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14067step0 raw14067; decide +kernel
      have hl : raw14067step0Labels = raw14067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14067 raw14067Labels permutation346 hz
    mixedMoment B raw14067step0 raw14067step0Labels = mixedMoment B raw14067step1 raw14067step1Labels := by
      have hz : ∀ j, raw14067step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14067step1 = (fun i j => raw14067step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14067step1 raw14067step0; decide +kernel
      have hl : raw14067step1Labels = raw14067step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14067step0 raw14067step0Labels permutation56 hz
    mixedMoment B raw14067step1 raw14067step1Labels = mixedMoment B raw14067step2 raw14067step2Labels := by
      have ha : raw14067step2 = (fun i j => raw14067step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14067step2 raw14067step1; decide +kernel
      have hl : raw14067step2Labels = raw14067step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14067step1 raw14067step1Labels permutation11 permutation2
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw14068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw14068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw14068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14068step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw14068step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14068step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw14068step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14068 raw14068Labels = mixedMoment B node5309 node5309Labels := by
  calc
    mixedMoment B raw14068 raw14068Labels = mixedMoment B raw14068step0 raw14068step0Labels := by
      have hz : ∀ j, raw14068 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14068step0 = (fun i j => raw14068 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14068step0 raw14068; decide +kernel
      have hl : raw14068step0Labels = raw14068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14068 raw14068Labels permutation590 hz
    mixedMoment B raw14068step0 raw14068step0Labels = mixedMoment B raw14068step1 raw14068step1Labels := by
      have hz : ∀ j, raw14068step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14068step1 = (fun i j => raw14068step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14068step1 raw14068step0; decide +kernel
      have hl : raw14068step1Labels = raw14068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14068step0 raw14068step0Labels permutation80 hz
    mixedMoment B raw14068step1 raw14068step1Labels = mixedMoment B raw14068step2 raw14068step2Labels := by
      have hz : ∀ j, raw14068step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw14068step2 = (fun i j => raw14068step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw14068step2 raw14068step1; decide +kernel
      have hl : raw14068step2Labels = raw14068step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14068step1 raw14068step1Labels permutation14 hz
    mixedMoment B raw14068step2 raw14068step2Labels = mixedMoment B raw14068step3 raw14068step3Labels := by
      have ha : raw14068step3 = (fun i j => raw14068step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14068step3 raw14068step2; decide +kernel
      have hl : raw14068step3Labels = raw14068step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14068step2 raw14068step2Labels permutation3 permutation2
    _ = mixedMoment B node5309 node5309Labels := by rfl

def raw14069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14069 raw14069Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw14069 raw14069Labels = mixedMoment B raw14069step0 raw14069step0Labels := by
      have hz : ∀ j, raw14069 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14069step0 = (fun i j => raw14069 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14069step0 raw14069; decide +kernel
      have hl : raw14069step0Labels = raw14069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14069 raw14069Labels permutation346 hz
    mixedMoment B raw14069step0 raw14069step0Labels = mixedMoment B raw14069step1 raw14069step1Labels := by
      have hz : ∀ j, raw14069step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14069step1 = (fun i j => raw14069step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14069step1 raw14069step0; decide +kernel
      have hl : raw14069step1Labels = raw14069step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14069step0 raw14069step0Labels permutation56 hz
    mixedMoment B raw14069step1 raw14069step1Labels = mixedMoment B raw14069step2 raw14069step2Labels := by
      have ha : raw14069step2 = (fun i j => raw14069step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14069step2 raw14069step1; decide +kernel
      have hl : raw14069step2Labels = raw14069step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14069step1 raw14069step1Labels permutation12 permutation2
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw14070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14070 raw14070Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw14070 raw14070Labels = mixedMoment B raw14070step0 raw14070step0Labels := by
      have hz : ∀ j, raw14070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14070step0 = (fun i j => raw14070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14070step0 raw14070; decide +kernel
      have hl : raw14070step0Labels = raw14070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14070 raw14070Labels permutation346 hz
    mixedMoment B raw14070step0 raw14070step0Labels = mixedMoment B raw14070step1 raw14070step1Labels := by
      have ha : raw14070step1 = (fun i j => raw14070step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14070step1 raw14070step0; decide +kernel
      have hl : raw14070step1Labels = raw14070step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14070step0 raw14070step0Labels permutation36 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw14071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14071 raw14071Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw14071 raw14071Labels = mixedMoment B raw14071step0 raw14071step0Labels := by
      have hz : ∀ j, raw14071 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14071step0 = (fun i j => raw14071 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14071step0 raw14071; decide +kernel
      have hl : raw14071step0Labels = raw14071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14071 raw14071Labels permutation265 hz
    mixedMoment B raw14071step0 raw14071step0Labels = mixedMoment B raw14071step1 raw14071step1Labels := by
      have ha : raw14071step1 = (fun i j => raw14071step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14071step1 raw14071step0; decide +kernel
      have hl : raw14071step1Labels = raw14071step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14071step0 raw14071step0Labels permutation36 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw14072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw14072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14072step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw14072step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14072 raw14072Labels = mixedMoment B node5309 node5309Labels := by
  calc
    mixedMoment B raw14072 raw14072Labels = mixedMoment B raw14072step0 raw14072step0Labels := by
      have hz : ∀ j, raw14072 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14072step0 = (fun i j => raw14072 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14072step0 raw14072; decide +kernel
      have hl : raw14072step0Labels = raw14072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14072 raw14072Labels permutation590 hz
    mixedMoment B raw14072step0 raw14072step0Labels = mixedMoment B raw14072step1 raw14072step1Labels := by
      have hz : ∀ j, raw14072step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14072step1 = (fun i j => raw14072step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14072step1 raw14072step0; decide +kernel
      have hl : raw14072step1Labels = raw14072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14072step0 raw14072step0Labels permutation80 hz
    mixedMoment B raw14072step1 raw14072step1Labels = mixedMoment B raw14072step2 raw14072step2Labels := by
      have hz : ∀ j, raw14072step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw14072step2 = (fun i j => raw14072step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw14072step2 raw14072step1; decide +kernel
      have hl : raw14072step2Labels = raw14072step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14072step1 raw14072step1Labels permutation14 hz
    _ = mixedMoment B node5309 node5309Labels := by rfl

def raw14073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14073step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14073step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14073 raw14073Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw14073 raw14073Labels = mixedMoment B raw14073step0 raw14073step0Labels := by
      have ha : raw14073step0 = (fun i j => raw14073 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14073step0 raw14073; decide +kernel
      have hl : raw14073step0Labels = raw14073Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14073 raw14073Labels permutation181 permutation7
    mixedMoment B raw14073step0 raw14073step0Labels = mixedMoment B raw14073step1 raw14073step1Labels := by
      have ha : raw14073step1 = -raw14073step0 := by apply Matrix.ext; change ∀ i j, raw14073step1 i j = -(raw14073step0 i j); unfold raw14073step1 raw14073step0; decide +kernel
      have hl : raw14073step1Labels = raw14073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14073step1 raw14073step1Labels = mixedMoment B raw14073step2 raw14073step2Labels := by
      have ha : raw14073step2 = raw14073step1 := by apply Matrix.ext; unfold raw14073step2 raw14073step1; decide +kernel
      have hl : raw14073step1Labels = labelEmbedding10 ∘ raw14073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14073step1 raw14073step1Labels raw14073step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw14074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14074step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14074step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14074step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14074step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14074 raw14074Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw14074 raw14074Labels = mixedMoment B raw14074step0 raw14074step0Labels := by
      have hz : ∀ j, raw14074 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14074step0 = (fun i j => raw14074 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14074step0 raw14074; decide +kernel
      have hl : raw14074step0Labels = raw14074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14074 raw14074Labels permutation265 hz
    mixedMoment B raw14074step0 raw14074step0Labels = mixedMoment B raw14074step1 raw14074step1Labels := by
      have ha : raw14074step1 = (fun i j => raw14074step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14074step1 raw14074step0; decide +kernel
      have hl : raw14074step1Labels = raw14074step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14074step0 raw14074step0Labels permutation37 permutation7
    mixedMoment B raw14074step1 raw14074step1Labels = mixedMoment B raw14074step2 raw14074step2Labels := by
      have ha : raw14074step2 = -raw14074step1 := by apply Matrix.ext; change ∀ i j, raw14074step2 i j = -(raw14074step1 i j); unfold raw14074step2 raw14074step1; decide +kernel
      have hl : raw14074step2Labels = raw14074step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14074step2 raw14074step2Labels = mixedMoment B raw14074step3 raw14074step3Labels := by
      have ha : raw14074step3 = raw14074step2 := by apply Matrix.ext; unfold raw14074step3 raw14074step2; decide +kernel
      have hl : raw14074step2Labels = labelEmbedding10 ∘ raw14074step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14074step2 raw14074step2Labels raw14074step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw14075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14075step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14075 raw14075Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw14075 raw14075Labels = mixedMoment B raw14075step0 raw14075step0Labels := by
      have hz : ∀ j, raw14075 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14075step0 = (fun i j => raw14075 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14075step0 raw14075; decide +kernel
      have hl : raw14075step0Labels = raw14075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14075 raw14075Labels permutation265 hz
    mixedMoment B raw14075step0 raw14075step0Labels = mixedMoment B raw14075step1 raw14075step1Labels := by
      have ha : raw14075step1 = (fun i j => raw14075step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14075step1 raw14075step0; decide +kernel
      have hl : raw14075step1Labels = raw14075step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14075step0 raw14075step0Labels permutation97 permutation6
    mixedMoment B raw14075step1 raw14075step1Labels = mixedMoment B raw14075step2 raw14075step2Labels := by
      have ha : raw14075step2 = raw14075step1 := by apply Matrix.ext; unfold raw14075step2 raw14075step1; decide +kernel
      have hl : raw14075step1Labels = labelEmbedding9 ∘ raw14075step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14075step1 raw14075step1Labels raw14075step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw14076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14076step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14076step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14076step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14076 raw14076Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw14076 raw14076Labels = mixedMoment B raw14076step0 raw14076step0Labels := by
      have hz : ∀ j, raw14076 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14076step0 = (fun i j => raw14076 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14076step0 raw14076; decide +kernel
      have hl : raw14076step0Labels = raw14076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14076 raw14076Labels permutation265 hz
    mixedMoment B raw14076step0 raw14076step0Labels = mixedMoment B raw14076step1 raw14076step1Labels := by
      have ha : raw14076step1 = (fun i j => raw14076step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14076step1 raw14076step0; decide +kernel
      have hl : raw14076step1Labels = raw14076step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14076step0 raw14076step0Labels permutation37 permutation7
    mixedMoment B raw14076step1 raw14076step1Labels = mixedMoment B raw14076step2 raw14076step2Labels := by
      have ha : raw14076step2 = -raw14076step1 := by apply Matrix.ext; change ∀ i j, raw14076step2 i j = -(raw14076step1 i j); unfold raw14076step2 raw14076step1; decide +kernel
      have hl : raw14076step2Labels = raw14076step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14076step2 raw14076step2Labels = mixedMoment B raw14076step3 raw14076step3Labels := by
      have ha : raw14076step3 = raw14076step2 := by apply Matrix.ext; unfold raw14076step3 raw14076step2; decide +kernel
      have hl : raw14076step2Labels = labelEmbedding10 ∘ raw14076step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14076step2 raw14076step2Labels raw14076step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw14077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14077step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14077step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14077step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14077step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14077step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14077step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14077step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14077 raw14077Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw14077 raw14077Labels = mixedMoment B raw14077step0 raw14077step0Labels := by
      have hz : ∀ j, raw14077 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14077step0 = (fun i j => raw14077 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14077step0 raw14077; decide +kernel
      have hl : raw14077step0Labels = raw14077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14077 raw14077Labels permutation590 hz
    mixedMoment B raw14077step0 raw14077step0Labels = mixedMoment B raw14077step1 raw14077step1Labels := by
      have hz : ∀ j, raw14077step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14077step1 = (fun i j => raw14077step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14077step1 raw14077step0; decide +kernel
      have hl : raw14077step1Labels = raw14077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14077step0 raw14077step0Labels permutation56 hz
    mixedMoment B raw14077step1 raw14077step1Labels = mixedMoment B raw14077step2 raw14077step2Labels := by
      have ha : raw14077step2 = (fun i j => raw14077step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14077step2 raw14077step1; decide +kernel
      have hl : raw14077step2Labels = raw14077step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14077step1 raw14077step1Labels permutation9 permutation7
    mixedMoment B raw14077step2 raw14077step2Labels = mixedMoment B raw14077step3 raw14077step3Labels := by
      have ha : raw14077step3 = -raw14077step2 := by apply Matrix.ext; change ∀ i j, raw14077step3 i j = -(raw14077step2 i j); unfold raw14077step3 raw14077step2; decide +kernel
      have hl : raw14077step3Labels = raw14077step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14077step3 raw14077step3Labels = mixedMoment B raw14077step4 raw14077step4Labels := by
      have ha : raw14077step4 = raw14077step3 := by apply Matrix.ext; unfold raw14077step4 raw14077step3; decide +kernel
      have hl : raw14077step3Labels = labelEmbedding10 ∘ raw14077step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14077step3 raw14077step3Labels raw14077step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw14078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14078 raw14078Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw14078 raw14078Labels = mixedMoment B raw14078step0 raw14078step0Labels := by
      have ha : raw14078step0 = (fun i j => raw14078 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14078step0 raw14078; decide +kernel
      have hl : raw14078step0Labels = raw14078Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14078 raw14078Labels permutation181 permutation2
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw14079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14079 raw14079Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw14079 raw14079Labels = mixedMoment B raw14079step0 raw14079step0Labels := by
      have ha : raw14079step0 = (fun i j => raw14079 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14079step0 raw14079; decide +kernel
      have hl : raw14079step0Labels = raw14079Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14079 raw14079Labels permutation181 permutation2
    _ = mixedMoment B node5098 node5098Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
