import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42880Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42880step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42880step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42880step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42880step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42880 raw42880Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw42880 raw42880Labels = mixedMoment B raw42880step0 raw42880step0Labels := by
      have ha : raw42880step0 = (fun i j => raw42880 (permutation251 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42880step0 raw42880; decide +kernel
      have hl : raw42880step0Labels = raw42880Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42880 raw42880Labels permutation251 permutation4
    mixedMoment B raw42880step0 raw42880step0Labels = mixedMoment B raw42880step1 raw42880step1Labels := by
      have ha : raw42880step1 = -raw42880step0 := by apply Matrix.ext; change ∀ i j, raw42880step1 i j = -(raw42880step0 i j); unfold raw42880step1 raw42880step0; decide +kernel
      have hl : raw42880step1Labels = raw42880step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42880step1 raw42880step1Labels = mixedMoment B raw42880step2 raw42880step2Labels := by
      have ha : raw42880step2 = raw42880step1 := by apply Matrix.ext; unfold raw42880step2 raw42880step1; decide +kernel
      have hl : raw42880step1Labels = labelEmbedding1 ∘ raw42880step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42880step1 raw42880step1Labels raw42880step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw42881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42881Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42881step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42881step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42881step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42881step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42881 raw42881Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw42881 raw42881Labels = mixedMoment B raw42881step0 raw42881step0Labels := by
      have ha : raw42881step0 = (fun i j => raw42881 (permutation251 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42881step0 raw42881; decide +kernel
      have hl : raw42881step0Labels = raw42881Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42881 raw42881Labels permutation251 permutation4
    mixedMoment B raw42881step0 raw42881step0Labels = mixedMoment B raw42881step1 raw42881step1Labels := by
      have ha : raw42881step1 = -raw42881step0 := by apply Matrix.ext; change ∀ i j, raw42881step1 i j = -(raw42881step0 i j); unfold raw42881step1 raw42881step0; decide +kernel
      have hl : raw42881step1Labels = raw42881step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42881step1 raw42881step1Labels = mixedMoment B raw42881step2 raw42881step2Labels := by
      have ha : raw42881step2 = raw42881step1 := by apply Matrix.ext; unfold raw42881step2 raw42881step1; decide +kernel
      have hl : raw42881step1Labels = labelEmbedding10 ∘ raw42881step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42881step1 raw42881step1Labels raw42881step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw42882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42882Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw42882step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw42882step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42882step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42882step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42882step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42882 raw42882Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw42882 raw42882Labels = mixedMoment B raw42882step0 raw42882step0Labels := by
      have hz : ∀ j, raw42882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42882step0 = (fun i j => raw42882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42882step0 raw42882; decide +kernel
      have hl : raw42882step0Labels = raw42882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42882 raw42882Labels permutation434 hz
    mixedMoment B raw42882step0 raw42882step0Labels = mixedMoment B raw42882step1 raw42882step1Labels := by
      have ha : raw42882step1 = (fun i j => raw42882step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42882step1 raw42882step0; decide +kernel
      have hl : raw42882step1Labels = raw42882step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42882step0 raw42882step0Labels permutation51 permutation4
    mixedMoment B raw42882step1 raw42882step1Labels = mixedMoment B raw42882step2 raw42882step2Labels := by
      have ha : raw42882step2 = -raw42882step1 := by apply Matrix.ext; change ∀ i j, raw42882step2 i j = -(raw42882step1 i j); unfold raw42882step2 raw42882step1; decide +kernel
      have hl : raw42882step2Labels = raw42882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42882step2 raw42882step2Labels = mixedMoment B raw42882step3 raw42882step3Labels := by
      have ha : raw42882step3 = raw42882step2 := by apply Matrix.ext; unfold raw42882step3 raw42882step2; decide +kernel
      have hl : raw42882step2Labels = labelEmbedding1 ∘ raw42882step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42882step2 raw42882step2Labels raw42882step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw42883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42883Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw42883step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw42883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw42883step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42883 raw42883Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw42883 raw42883Labels = mixedMoment B raw42883step0 raw42883step0Labels := by
      have hz : ∀ j, raw42883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42883step0 = (fun i j => raw42883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42883step0 raw42883; decide +kernel
      have hl : raw42883step0Labels = raw42883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42883 raw42883Labels permutation434 hz
    mixedMoment B raw42883step0 raw42883step0Labels = mixedMoment B raw42883step1 raw42883step1Labels := by
      have ha : raw42883step1 = (fun i j => raw42883step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42883step1 raw42883step0; decide +kernel
      have hl : raw42883step1Labels = raw42883step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42883step0 raw42883step0Labels permutation89 permutation6
    mixedMoment B raw42883step1 raw42883step1Labels = mixedMoment B raw42883step2 raw42883step2Labels := by
      have ha : raw42883step2 = -raw42883step1 := by apply Matrix.ext; change ∀ i j, raw42883step2 i j = -(raw42883step1 i j); unfold raw42883step2 raw42883step1; decide +kernel
      have hl : raw42883step2Labels = raw42883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw42884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42884Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42884step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw42884step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42884step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42884step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42884step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42884 raw42884Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw42884 raw42884Labels = mixedMoment B raw42884step0 raw42884step0Labels := by
      have hz : ∀ j, raw42884 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42884step0 = (fun i j => raw42884 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42884step0 raw42884; decide +kernel
      have hl : raw42884step0Labels = raw42884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42884 raw42884Labels permutation434 hz
    mixedMoment B raw42884step0 raw42884step0Labels = mixedMoment B raw42884step1 raw42884step1Labels := by
      have ha : raw42884step1 = (fun i j => raw42884step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42884step1 raw42884step0; decide +kernel
      have hl : raw42884step1Labels = raw42884step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42884step0 raw42884step0Labels permutation54 permutation4
    mixedMoment B raw42884step1 raw42884step1Labels = mixedMoment B raw42884step2 raw42884step2Labels := by
      have ha : raw42884step2 = -raw42884step1 := by apply Matrix.ext; change ∀ i j, raw42884step2 i j = -(raw42884step1 i j); unfold raw42884step2 raw42884step1; decide +kernel
      have hl : raw42884step2Labels = raw42884step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42884step2 raw42884step2Labels = mixedMoment B raw42884step3 raw42884step3Labels := by
      have ha : raw42884step3 = raw42884step2 := by apply Matrix.ext; unfold raw42884step3 raw42884step2; decide +kernel
      have hl : raw42884step2Labels = labelEmbedding1 ∘ raw42884step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42884step2 raw42884step2Labels raw42884step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

def raw42885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42885Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42885step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw42885step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42885step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42885step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42885step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42885 raw42885Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw42885 raw42885Labels = mixedMoment B raw42885step0 raw42885step0Labels := by
      have hz : ∀ j, raw42885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42885step0 = (fun i j => raw42885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42885step0 raw42885; decide +kernel
      have hl : raw42885step0Labels = raw42885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42885 raw42885Labels permutation434 hz
    mixedMoment B raw42885step0 raw42885step0Labels = mixedMoment B raw42885step1 raw42885step1Labels := by
      have ha : raw42885step1 = (fun i j => raw42885step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42885step1 raw42885step0; decide +kernel
      have hl : raw42885step1Labels = raw42885step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42885step0 raw42885step0Labels permutation54 permutation4
    mixedMoment B raw42885step1 raw42885step1Labels = mixedMoment B raw42885step2 raw42885step2Labels := by
      have ha : raw42885step2 = -raw42885step1 := by apply Matrix.ext; change ∀ i j, raw42885step2 i j = -(raw42885step1 i j); unfold raw42885step2 raw42885step1; decide +kernel
      have hl : raw42885step2Labels = raw42885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42885step2 raw42885step2Labels = mixedMoment B raw42885step3 raw42885step3Labels := by
      have ha : raw42885step3 = raw42885step2 := by apply Matrix.ext; unfold raw42885step3 raw42885step2; decide +kernel
      have hl : raw42885step2Labels = labelEmbedding10 ∘ raw42885step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42885step2 raw42885step2Labels raw42885step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw42886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42886Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw42886step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![3, -3, 0]]
def raw42886step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42886step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42886step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42886step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42886 raw42886Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw42886 raw42886Labels = mixedMoment B raw42886step0 raw42886step0Labels := by
      have hz : ∀ j, raw42886 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42886step0 = (fun i j => raw42886 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42886step0 raw42886; decide +kernel
      have hl : raw42886step0Labels = raw42886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42886 raw42886Labels permutation520 hz
    mixedMoment B raw42886step0 raw42886step0Labels = mixedMoment B raw42886step1 raw42886step1Labels := by
      have hz : ∀ j, raw42886step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42886step1 = (fun i j => raw42886step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42886step1 raw42886step0; decide +kernel
      have hl : raw42886step1Labels = raw42886step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42886step0 raw42886step0Labels permutation104 hz
    mixedMoment B raw42886step1 raw42886step1Labels = mixedMoment B raw42886step2 raw42886step2Labels := by
      have ha : raw42886step2 = (fun i j => raw42886step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42886step2 raw42886step1; decide +kernel
      have hl : raw42886step2Labels = raw42886step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42886step1 raw42886step1Labels permutation31 permutation4
    mixedMoment B raw42886step2 raw42886step2Labels = mixedMoment B raw42886step3 raw42886step3Labels := by
      have ha : raw42886step3 = raw42886step2 := by apply Matrix.ext; unfold raw42886step3 raw42886step2; decide +kernel
      have hl : raw42886step2Labels = labelEmbedding1 ∘ raw42886step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42886step2 raw42886step2Labels raw42886step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw42887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42887Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw42887step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![3, -3, 0]]
def raw42887step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42887step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42887step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42887step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42887step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42887 raw42887Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw42887 raw42887Labels = mixedMoment B raw42887step0 raw42887step0Labels := by
      have hz : ∀ j, raw42887 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42887step0 = (fun i j => raw42887 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42887step0 raw42887; decide +kernel
      have hl : raw42887step0Labels = raw42887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42887 raw42887Labels permutation520 hz
    mixedMoment B raw42887step0 raw42887step0Labels = mixedMoment B raw42887step1 raw42887step1Labels := by
      have hz : ∀ j, raw42887step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42887step1 = (fun i j => raw42887step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42887step1 raw42887step0; decide +kernel
      have hl : raw42887step1Labels = raw42887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42887step0 raw42887step0Labels permutation104 hz
    mixedMoment B raw42887step1 raw42887step1Labels = mixedMoment B raw42887step2 raw42887step2Labels := by
      have ha : raw42887step2 = (fun i j => raw42887step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42887step2 raw42887step1; decide +kernel
      have hl : raw42887step2Labels = raw42887step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42887step1 raw42887step1Labels permutation31 permutation5
    mixedMoment B raw42887step2 raw42887step2Labels = mixedMoment B raw42887step3 raw42887step3Labels := by
      have ha : raw42887step3 = raw42887step2 := by apply Matrix.ext; unfold raw42887step3 raw42887step2; decide +kernel
      have hl : raw42887step2Labels = labelEmbedding9 ∘ raw42887step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42887step2 raw42887step2Labels raw42887step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw42888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42888Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1]]
def raw42888step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42888step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42888step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42888 raw42888Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw42888 raw42888Labels = mixedMoment B raw42888step0 raw42888step0Labels := by
      have hz : ∀ j, raw42888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42888step0 = (fun i j => raw42888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42888step0 raw42888; decide +kernel
      have hl : raw42888step0Labels = raw42888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42888 raw42888Labels permutation434 hz
    mixedMoment B raw42888step0 raw42888step0Labels = mixedMoment B raw42888step1 raw42888step1Labels := by
      have ha : raw42888step1 = (fun i j => raw42888step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42888step1 raw42888step0; decide +kernel
      have hl : raw42888step1Labels = raw42888step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42888step0 raw42888step0Labels permutation145 permutation4
    mixedMoment B raw42888step1 raw42888step1Labels = mixedMoment B raw42888step2 raw42888step2Labels := by
      have ha : raw42888step2 = raw42888step1 := by apply Matrix.ext; unfold raw42888step2 raw42888step1; decide +kernel
      have hl : raw42888step1Labels = labelEmbedding1 ∘ raw42888step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42888step1 raw42888step1Labels raw42888step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw42889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42889Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1]]
def raw42889step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42889step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42889 raw42889Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw42889 raw42889Labels = mixedMoment B raw42889step0 raw42889step0Labels := by
      have hz : ∀ j, raw42889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42889step0 = (fun i j => raw42889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42889step0 raw42889; decide +kernel
      have hl : raw42889step0Labels = raw42889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42889 raw42889Labels permutation434 hz
    mixedMoment B raw42889step0 raw42889step0Labels = mixedMoment B raw42889step1 raw42889step1Labels := by
      have ha : raw42889step1 = (fun i j => raw42889step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42889step1 raw42889step0; decide +kernel
      have hl : raw42889step1Labels = raw42889step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42889step0 raw42889step0Labels permutation151 permutation5
    mixedMoment B raw42889step1 raw42889step1Labels = mixedMoment B raw42889step2 raw42889step2Labels := by
      have ha : raw42889step2 = raw42889step1 := by apply Matrix.ext; unfold raw42889step2 raw42889step1; decide +kernel
      have hl : raw42889step1Labels = labelEmbedding9 ∘ raw42889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42889step1 raw42889step1Labels raw42889step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw42890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42890Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw42890step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42890step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42890step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42890step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42890step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42890 raw42890Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw42890 raw42890Labels = mixedMoment B raw42890step0 raw42890step0Labels := by
      have hz : ∀ j, raw42890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42890step0 = (fun i j => raw42890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42890step0 raw42890; decide +kernel
      have hl : raw42890step0Labels = raw42890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42890 raw42890Labels permutation434 hz
    mixedMoment B raw42890step0 raw42890step0Labels = mixedMoment B raw42890step1 raw42890step1Labels := by
      have ha : raw42890step1 = (fun i j => raw42890step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42890step1 raw42890step0; decide +kernel
      have hl : raw42890step1Labels = raw42890step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42890step0 raw42890step0Labels permutation32 permutation4
    mixedMoment B raw42890step1 raw42890step1Labels = mixedMoment B raw42890step2 raw42890step2Labels := by
      have ha : raw42890step2 = -raw42890step1 := by apply Matrix.ext; change ∀ i j, raw42890step2 i j = -(raw42890step1 i j); unfold raw42890step2 raw42890step1; decide +kernel
      have hl : raw42890step2Labels = raw42890step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42890step2 raw42890step2Labels = mixedMoment B raw42890step3 raw42890step3Labels := by
      have ha : raw42890step3 = raw42890step2 := by apply Matrix.ext; unfold raw42890step3 raw42890step2; decide +kernel
      have hl : raw42890step2Labels = labelEmbedding1 ∘ raw42890step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42890step2 raw42890step2Labels raw42890step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw42891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42891Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw42891step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42891step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42891 raw42891Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw42891 raw42891Labels = mixedMoment B raw42891step0 raw42891step0Labels := by
      have hz : ∀ j, raw42891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42891step0 = (fun i j => raw42891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42891step0 raw42891; decide +kernel
      have hl : raw42891step0Labels = raw42891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42891 raw42891Labels permutation434 hz
    mixedMoment B raw42891step0 raw42891step0Labels = mixedMoment B raw42891step1 raw42891step1Labels := by
      have ha : raw42891step1 = (fun i j => raw42891step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42891step1 raw42891step0; decide +kernel
      have hl : raw42891step1Labels = raw42891step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42891step0 raw42891step0Labels permutation151 permutation5
    mixedMoment B raw42891step1 raw42891step1Labels = mixedMoment B raw42891step2 raw42891step2Labels := by
      have ha : raw42891step2 = raw42891step1 := by apply Matrix.ext; unfold raw42891step2 raw42891step1; decide +kernel
      have hl : raw42891step1Labels = labelEmbedding9 ∘ raw42891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42891step1 raw42891step1Labels raw42891step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw42892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42892Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw42892step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42892step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42892step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42892step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42892 raw42892Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw42892 raw42892Labels = mixedMoment B raw42892step0 raw42892step0Labels := by
      have hz : ∀ j, raw42892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42892step0 = (fun i j => raw42892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42892step0 raw42892; decide +kernel
      have hl : raw42892step0Labels = raw42892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42892 raw42892Labels permutation434 hz
    mixedMoment B raw42892step0 raw42892step0Labels = mixedMoment B raw42892step1 raw42892step1Labels := by
      have ha : raw42892step1 = (fun i j => raw42892step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42892step1 raw42892step0; decide +kernel
      have hl : raw42892step1Labels = raw42892step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42892step0 raw42892step0Labels permutation33 permutation4
    mixedMoment B raw42892step1 raw42892step1Labels = mixedMoment B raw42892step2 raw42892step2Labels := by
      have ha : raw42892step2 = -raw42892step1 := by apply Matrix.ext; change ∀ i j, raw42892step2 i j = -(raw42892step1 i j); unfold raw42892step2 raw42892step1; decide +kernel
      have hl : raw42892step2Labels = raw42892step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42892step2 raw42892step2Labels = mixedMoment B raw42892step3 raw42892step3Labels := by
      have ha : raw42892step3 = raw42892step2 := by apply Matrix.ext; unfold raw42892step3 raw42892step2; decide +kernel
      have hl : raw42892step2Labels = labelEmbedding1 ∘ raw42892step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42892step2 raw42892step2Labels raw42892step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw42893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42893Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw42893step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42893step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42893 raw42893Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw42893 raw42893Labels = mixedMoment B raw42893step0 raw42893step0Labels := by
      have hz : ∀ j, raw42893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42893step0 = (fun i j => raw42893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42893step0 raw42893; decide +kernel
      have hl : raw42893step0Labels = raw42893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42893 raw42893Labels permutation434 hz
    mixedMoment B raw42893step0 raw42893step0Labels = mixedMoment B raw42893step1 raw42893step1Labels := by
      have ha : raw42893step1 = (fun i j => raw42893step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42893step1 raw42893step0; decide +kernel
      have hl : raw42893step1Labels = raw42893step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42893step0 raw42893step0Labels permutation127 permutation5
    mixedMoment B raw42893step1 raw42893step1Labels = mixedMoment B raw42893step2 raw42893step2Labels := by
      have ha : raw42893step2 = raw42893step1 := by apply Matrix.ext; unfold raw42893step2 raw42893step1; decide +kernel
      have hl : raw42893step1Labels = labelEmbedding9 ∘ raw42893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42893step1 raw42893step1Labels raw42893step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw42894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42894Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42894step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42894step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42894 raw42894Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw42894 raw42894Labels = mixedMoment B raw42894step0 raw42894step0Labels := by
      have ha : raw42894step0 = (fun i j => raw42894 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42894step0 raw42894; decide +kernel
      have hl : raw42894step0Labels = raw42894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42894 raw42894Labels permutation164 permutation4
    mixedMoment B raw42894step0 raw42894step0Labels = mixedMoment B raw42894step1 raw42894step1Labels := by
      have ha : raw42894step1 = -raw42894step0 := by apply Matrix.ext; change ∀ i j, raw42894step1 i j = -(raw42894step0 i j); unfold raw42894step1 raw42894step0; decide +kernel
      have hl : raw42894step1Labels = raw42894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42894step1 raw42894step1Labels = mixedMoment B raw42894step2 raw42894step2Labels := by
      have ha : raw42894step2 = raw42894step1 := by apply Matrix.ext; unfold raw42894step2 raw42894step1; decide +kernel
      have hl : raw42894step1Labels = labelEmbedding1 ∘ raw42894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42894step1 raw42894step1Labels raw42894step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw42895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42895Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42895step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42895 raw42895Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw42895 raw42895Labels = mixedMoment B raw42895step0 raw42895step0Labels := by
      have ha : raw42895step0 = (fun i j => raw42895 (permutation664 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42895step0 raw42895; decide +kernel
      have hl : raw42895step0Labels = raw42895Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42895 raw42895Labels permutation664 permutation5
    mixedMoment B raw42895step0 raw42895step0Labels = mixedMoment B raw42895step1 raw42895step1Labels := by
      have ha : raw42895step1 = raw42895step0 := by apply Matrix.ext; unfold raw42895step1 raw42895step0; decide +kernel
      have hl : raw42895step0Labels = labelEmbedding9 ∘ raw42895step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42895step0 raw42895step0Labels raw42895step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw42896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42896Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42896step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42896step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42896step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42896 raw42896Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw42896 raw42896Labels = mixedMoment B raw42896step0 raw42896step0Labels := by
      have ha : raw42896step0 = (fun i j => raw42896 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42896step0 raw42896; decide +kernel
      have hl : raw42896step0Labels = raw42896Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42896 raw42896Labels permutation683 permutation2
    mixedMoment B raw42896step0 raw42896step0Labels = mixedMoment B raw42896step1 raw42896step1Labels := by
      have ha : raw42896step1 = -raw42896step0 := by apply Matrix.ext; change ∀ i j, raw42896step1 i j = -(raw42896step0 i j); unfold raw42896step1 raw42896step0; decide +kernel
      have hl : raw42896step1Labels = raw42896step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42896step1 raw42896step1Labels = mixedMoment B raw42896step2 raw42896step2Labels := by
      have ha : raw42896step2 = raw42896step1 := by apply Matrix.ext; unfold raw42896step2 raw42896step1; decide +kernel
      have hl : raw42896step1Labels = labelEmbedding1 ∘ raw42896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42896step1 raw42896step1Labels raw42896step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw42897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42897Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42897step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42897step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42897 raw42897Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw42897 raw42897Labels = mixedMoment B raw42897step0 raw42897step0Labels := by
      have ha : raw42897step0 = (fun i j => raw42897 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42897step0 raw42897; decide +kernel
      have hl : raw42897step0Labels = raw42897Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42897 raw42897Labels permutation688 permutation3
    mixedMoment B raw42897step0 raw42897step0Labels = mixedMoment B raw42897step1 raw42897step1Labels := by
      have ha : raw42897step1 = -raw42897step0 := by apply Matrix.ext; change ∀ i j, raw42897step1 i j = -(raw42897step0 i j); unfold raw42897step1 raw42897step0; decide +kernel
      have hl : raw42897step1Labels = raw42897step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42897step1 raw42897step1Labels = mixedMoment B raw42897step2 raw42897step2Labels := by
      have ha : raw42897step2 = raw42897step1 := by apply Matrix.ext; unfold raw42897step2 raw42897step1; decide +kernel
      have hl : raw42897step1Labels = labelEmbedding7 ∘ raw42897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42897step1 raw42897step1Labels raw42897step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw42898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42898Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42898 raw42898Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw42898 raw42898Labels = mixedMoment B raw42898step0 raw42898step0Labels := by
      have ha : raw42898step0 = (fun i j => raw42898 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42898step0 raw42898; decide +kernel
      have hl : raw42898step0Labels = raw42898Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42898 raw42898Labels permutation683 permutation2
    mixedMoment B raw42898step0 raw42898step0Labels = mixedMoment B raw42898step1 raw42898step1Labels := by
      have ha : raw42898step1 = -raw42898step0 := by apply Matrix.ext; change ∀ i j, raw42898step1 i j = -(raw42898step0 i j); unfold raw42898step1 raw42898step0; decide +kernel
      have hl : raw42898step1Labels = raw42898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42898step1 raw42898step1Labels = mixedMoment B raw42898step2 raw42898step2Labels := by
      have ha : raw42898step2 = raw42898step1 := by apply Matrix.ext; unfold raw42898step2 raw42898step1; decide +kernel
      have hl : raw42898step1Labels = labelEmbedding1 ∘ raw42898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42898step1 raw42898step1Labels raw42898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw42899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42899Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42899step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42899step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42899step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42899step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42899 raw42899Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw42899 raw42899Labels = mixedMoment B raw42899step0 raw42899step0Labels := by
      have ha : raw42899step0 = (fun i j => raw42899 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42899step0 raw42899; decide +kernel
      have hl : raw42899step0Labels = raw42899Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42899 raw42899Labels permutation683 permutation2
    mixedMoment B raw42899step0 raw42899step0Labels = mixedMoment B raw42899step1 raw42899step1Labels := by
      have ha : raw42899step1 = -raw42899step0 := by apply Matrix.ext; change ∀ i j, raw42899step1 i j = -(raw42899step0 i j); unfold raw42899step1 raw42899step0; decide +kernel
      have hl : raw42899step1Labels = raw42899step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42899step1 raw42899step1Labels = mixedMoment B raw42899step2 raw42899step2Labels := by
      have ha : raw42899step2 = raw42899step1 := by apply Matrix.ext; unfold raw42899step2 raw42899step1; decide +kernel
      have hl : raw42899step1Labels = labelEmbedding8 ∘ raw42899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42899step1 raw42899step1Labels raw42899step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw42900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42900Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42900step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42900 raw42900Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw42900 raw42900Labels = mixedMoment B raw42900step0 raw42900step0Labels := by
      have ha : raw42900step0 = (fun i j => raw42900 (permutation498 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42900step0 raw42900; decide +kernel
      have hl : raw42900step0Labels = raw42900Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42900 raw42900Labels permutation498 permutation4
    mixedMoment B raw42900step0 raw42900step0Labels = mixedMoment B raw42900step1 raw42900step1Labels := by
      have ha : raw42900step1 = raw42900step0 := by apply Matrix.ext; unfold raw42900step1 raw42900step0; decide +kernel
      have hl : raw42900step0Labels = labelEmbedding1 ∘ raw42900step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42900step0 raw42900step0Labels raw42900step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw42901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42901Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42901 raw42901Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42901 raw42901Labels = mixedMoment B raw42901step0 raw42901step0Labels := by
      have ha : raw42901step0 = (fun i j => raw42901 (permutation477 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42901step0 raw42901; decide +kernel
      have hl : raw42901step0Labels = raw42901Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42901 raw42901Labels permutation477 permutation6
    mixedMoment B raw42901step0 raw42901step0Labels = mixedMoment B raw42901step1 raw42901step1Labels := by
      have ha : raw42901step1 = -raw42901step0 := by apply Matrix.ext; change ∀ i j, raw42901step1 i j = -(raw42901step0 i j); unfold raw42901step1 raw42901step0; decide +kernel
      have hl : raw42901step1Labels = raw42901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw42902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42902Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw42902step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42902step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42902step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42902step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42902 raw42902Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw42902 raw42902Labels = mixedMoment B raw42902step0 raw42902step0Labels := by
      have hz : ∀ j, raw42902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42902step0 = (fun i j => raw42902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42902step0 raw42902; decide +kernel
      have hl : raw42902step0Labels = raw42902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42902 raw42902Labels permutation434 hz
    mixedMoment B raw42902step0 raw42902step0Labels = mixedMoment B raw42902step1 raw42902step1Labels := by
      have ha : raw42902step1 = (fun i j => raw42902step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42902step1 raw42902step0; decide +kernel
      have hl : raw42902step1Labels = raw42902step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42902step0 raw42902step0Labels permutation34 permutation4
    mixedMoment B raw42902step1 raw42902step1Labels = mixedMoment B raw42902step2 raw42902step2Labels := by
      have ha : raw42902step2 = -raw42902step1 := by apply Matrix.ext; change ∀ i j, raw42902step2 i j = -(raw42902step1 i j); unfold raw42902step2 raw42902step1; decide +kernel
      have hl : raw42902step2Labels = raw42902step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42902step2 raw42902step2Labels = mixedMoment B raw42902step3 raw42902step3Labels := by
      have ha : raw42902step3 = raw42902step2 := by apply Matrix.ext; unfold raw42902step3 raw42902step2; decide +kernel
      have hl : raw42902step2Labels = labelEmbedding1 ∘ raw42902step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42902step2 raw42902step2Labels raw42902step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw42903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42903Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw42903step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42903step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42903step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42903step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42903step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42903 raw42903Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw42903 raw42903Labels = mixedMoment B raw42903step0 raw42903step0Labels := by
      have hz : ∀ j, raw42903 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42903step0 = (fun i j => raw42903 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42903step0 raw42903; decide +kernel
      have hl : raw42903step0Labels = raw42903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42903 raw42903Labels permutation434 hz
    mixedMoment B raw42903step0 raw42903step0Labels = mixedMoment B raw42903step1 raw42903step1Labels := by
      have ha : raw42903step1 = (fun i j => raw42903step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42903step1 raw42903step0; decide +kernel
      have hl : raw42903step1Labels = raw42903step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42903step0 raw42903step0Labels permutation151 permutation3
    mixedMoment B raw42903step1 raw42903step1Labels = mixedMoment B raw42903step2 raw42903step2Labels := by
      have ha : raw42903step2 = -raw42903step1 := by apply Matrix.ext; change ∀ i j, raw42903step2 i j = -(raw42903step1 i j); unfold raw42903step2 raw42903step1; decide +kernel
      have hl : raw42903step2Labels = raw42903step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42903step2 raw42903step2Labels = mixedMoment B raw42903step3 raw42903step3Labels := by
      have ha : raw42903step3 = raw42903step2 := by apply Matrix.ext; unfold raw42903step3 raw42903step2; decide +kernel
      have hl : raw42903step2Labels = labelEmbedding7 ∘ raw42903step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42903step2 raw42903step2Labels raw42903step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw42904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42904Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw42904step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42904step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42904step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42904step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42904step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42904 raw42904Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw42904 raw42904Labels = mixedMoment B raw42904step0 raw42904step0Labels := by
      have hz : ∀ j, raw42904 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42904step0 = (fun i j => raw42904 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42904step0 raw42904; decide +kernel
      have hl : raw42904step0Labels = raw42904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42904 raw42904Labels permutation434 hz
    mixedMoment B raw42904step0 raw42904step0Labels = mixedMoment B raw42904step1 raw42904step1Labels := by
      have ha : raw42904step1 = (fun i j => raw42904step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42904step1 raw42904step0; decide +kernel
      have hl : raw42904step1Labels = raw42904step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42904step0 raw42904step0Labels permutation146 permutation2
    mixedMoment B raw42904step1 raw42904step1Labels = mixedMoment B raw42904step2 raw42904step2Labels := by
      have ha : raw42904step2 = -raw42904step1 := by apply Matrix.ext; change ∀ i j, raw42904step2 i j = -(raw42904step1 i j); unfold raw42904step2 raw42904step1; decide +kernel
      have hl : raw42904step2Labels = raw42904step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42904step2 raw42904step2Labels = mixedMoment B raw42904step3 raw42904step3Labels := by
      have ha : raw42904step3 = raw42904step2 := by apply Matrix.ext; unfold raw42904step3 raw42904step2; decide +kernel
      have hl : raw42904step2Labels = labelEmbedding1 ∘ raw42904step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42904step2 raw42904step2Labels raw42904step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

def raw42905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42905Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw42905step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42905step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42905step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42905step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42905step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42905step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42905 raw42905Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw42905 raw42905Labels = mixedMoment B raw42905step0 raw42905step0Labels := by
      have hz : ∀ j, raw42905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42905step0 = (fun i j => raw42905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42905step0 raw42905; decide +kernel
      have hl : raw42905step0Labels = raw42905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42905 raw42905Labels permutation434 hz
    mixedMoment B raw42905step0 raw42905step0Labels = mixedMoment B raw42905step1 raw42905step1Labels := by
      have ha : raw42905step1 = (fun i j => raw42905step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42905step1 raw42905step0; decide +kernel
      have hl : raw42905step1Labels = raw42905step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42905step0 raw42905step0Labels permutation151 permutation3
    mixedMoment B raw42905step1 raw42905step1Labels = mixedMoment B raw42905step2 raw42905step2Labels := by
      have ha : raw42905step2 = -raw42905step1 := by apply Matrix.ext; change ∀ i j, raw42905step2 i j = -(raw42905step1 i j); unfold raw42905step2 raw42905step1; decide +kernel
      have hl : raw42905step2Labels = raw42905step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42905step2 raw42905step2Labels = mixedMoment B raw42905step3 raw42905step3Labels := by
      have ha : raw42905step3 = raw42905step2 := by apply Matrix.ext; unfold raw42905step3 raw42905step2; decide +kernel
      have hl : raw42905step2Labels = labelEmbedding7 ∘ raw42905step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42905step2 raw42905step2Labels raw42905step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw42906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42906Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42906step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42906step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42906step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42906 raw42906Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw42906 raw42906Labels = mixedMoment B raw42906step0 raw42906step0Labels := by
      have ha : raw42906step0 = (fun i j => raw42906 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42906step0 raw42906; decide +kernel
      have hl : raw42906step0Labels = raw42906Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42906 raw42906Labels permutation683 permutation2
    mixedMoment B raw42906step0 raw42906step0Labels = mixedMoment B raw42906step1 raw42906step1Labels := by
      have ha : raw42906step1 = -raw42906step0 := by apply Matrix.ext; change ∀ i j, raw42906step1 i j = -(raw42906step0 i j); unfold raw42906step1 raw42906step0; decide +kernel
      have hl : raw42906step1Labels = raw42906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42906step1 raw42906step1Labels = mixedMoment B raw42906step2 raw42906step2Labels := by
      have ha : raw42906step2 = raw42906step1 := by apply Matrix.ext; unfold raw42906step2 raw42906step1; decide +kernel
      have hl : raw42906step1Labels = labelEmbedding1 ∘ raw42906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42906step1 raw42906step1Labels raw42906step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw42907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42907Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42907step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42907step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42907 raw42907Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42907 raw42907Labels = mixedMoment B raw42907step0 raw42907step0Labels := by
      have ha : raw42907step0 = (fun i j => raw42907 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42907step0 raw42907; decide +kernel
      have hl : raw42907step0Labels = raw42907Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42907 raw42907Labels permutation683 permutation2
    mixedMoment B raw42907step0 raw42907step0Labels = mixedMoment B raw42907step1 raw42907step1Labels := by
      have ha : raw42907step1 = -raw42907step0 := by apply Matrix.ext; change ∀ i j, raw42907step1 i j = -(raw42907step0 i j); unfold raw42907step1 raw42907step0; decide +kernel
      have hl : raw42907step1Labels = raw42907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42907step1 raw42907step1Labels = mixedMoment B raw42907step2 raw42907step2Labels := by
      have ha : raw42907step2 = raw42907step1 := by apply Matrix.ext; unfold raw42907step2 raw42907step1; decide +kernel
      have hl : raw42907step1Labels = labelEmbedding8 ∘ raw42907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42907step1 raw42907step1Labels raw42907step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw42908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42908Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw42908step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42908step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42908 raw42908Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw42908 raw42908Labels = mixedMoment B raw42908step0 raw42908step0Labels := by
      have hz : ∀ j, raw42908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42908step0 = (fun i j => raw42908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42908step0 raw42908; decide +kernel
      have hl : raw42908step0Labels = raw42908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42908 raw42908Labels permutation434 hz
    mixedMoment B raw42908step0 raw42908step0Labels = mixedMoment B raw42908step1 raw42908step1Labels := by
      have ha : raw42908step1 = (fun i j => raw42908step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42908step1 raw42908step0; decide +kernel
      have hl : raw42908step1Labels = raw42908step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42908step0 raw42908step0Labels permutation97 permutation4
    mixedMoment B raw42908step1 raw42908step1Labels = mixedMoment B raw42908step2 raw42908step2Labels := by
      have ha : raw42908step2 = raw42908step1 := by apply Matrix.ext; unfold raw42908step2 raw42908step1; decide +kernel
      have hl : raw42908step1Labels = labelEmbedding1 ∘ raw42908step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42908step1 raw42908step1Labels raw42908step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw42909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42909Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw42909step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42909step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42909step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42909 raw42909Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42909 raw42909Labels = mixedMoment B raw42909step0 raw42909step0Labels := by
      have hz : ∀ j, raw42909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42909step0 = (fun i j => raw42909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42909step0 raw42909; decide +kernel
      have hl : raw42909step0Labels = raw42909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42909 raw42909Labels permutation434 hz
    mixedMoment B raw42909step0 raw42909step0Labels = mixedMoment B raw42909step1 raw42909step1Labels := by
      have ha : raw42909step1 = (fun i j => raw42909step0 (permutation94 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42909step1 raw42909step0; decide +kernel
      have hl : raw42909step1Labels = raw42909step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42909step0 raw42909step0Labels permutation94 permutation6
    mixedMoment B raw42909step1 raw42909step1Labels = mixedMoment B raw42909step2 raw42909step2Labels := by
      have ha : raw42909step2 = -raw42909step1 := by apply Matrix.ext; change ∀ i j, raw42909step2 i j = -(raw42909step1 i j); unfold raw42909step2 raw42909step1; decide +kernel
      have hl : raw42909step2Labels = raw42909step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw42910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42910Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw42910step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42910step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42910 raw42910Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw42910 raw42910Labels = mixedMoment B raw42910step0 raw42910step0Labels := by
      have hz : ∀ j, raw42910 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42910step0 = (fun i j => raw42910 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42910step0 raw42910; decide +kernel
      have hl : raw42910step0Labels = raw42910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42910 raw42910Labels permutation520 hz
    mixedMoment B raw42910step0 raw42910step0Labels = mixedMoment B raw42910step1 raw42910step1Labels := by
      have ha : raw42910step1 = (fun i j => raw42910step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42910step1 raw42910step0; decide +kernel
      have hl : raw42910step1Labels = raw42910step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42910step0 raw42910step0Labels permutation137 permutation4
    mixedMoment B raw42910step1 raw42910step1Labels = mixedMoment B raw42910step2 raw42910step2Labels := by
      have ha : raw42910step2 = raw42910step1 := by apply Matrix.ext; unfold raw42910step2 raw42910step1; decide +kernel
      have hl : raw42910step1Labels = labelEmbedding1 ∘ raw42910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42910step1 raw42910step1Labels raw42910step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw42911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42911Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw42911step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42911step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42911step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42911 raw42911Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw42911 raw42911Labels = mixedMoment B raw42911step0 raw42911step0Labels := by
      have hz : ∀ j, raw42911 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42911step0 = (fun i j => raw42911 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42911step0 raw42911; decide +kernel
      have hl : raw42911step0Labels = raw42911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42911 raw42911Labels permutation520 hz
    mixedMoment B raw42911step0 raw42911step0Labels = mixedMoment B raw42911step1 raw42911step1Labels := by
      have ha : raw42911step1 = (fun i j => raw42911step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42911step1 raw42911step0; decide +kernel
      have hl : raw42911step1Labels = raw42911step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42911step0 raw42911step0Labels permutation137 permutation5
    mixedMoment B raw42911step1 raw42911step1Labels = mixedMoment B raw42911step2 raw42911step2Labels := by
      have ha : raw42911step2 = raw42911step1 := by apply Matrix.ext; unfold raw42911step2 raw42911step1; decide +kernel
      have hl : raw42911step1Labels = labelEmbedding9 ∘ raw42911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42911step1 raw42911step1Labels raw42911step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw42912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42912Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42912step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42912 raw42912Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw42912 raw42912Labels = mixedMoment B raw42912step0 raw42912step0Labels := by
      have ha : raw42912step0 = (fun i j => raw42912 (permutation611 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42912step0 raw42912; decide +kernel
      have hl : raw42912step0Labels = raw42912Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42912 raw42912Labels permutation611 permutation4
    mixedMoment B raw42912step0 raw42912step0Labels = mixedMoment B raw42912step1 raw42912step1Labels := by
      have ha : raw42912step1 = raw42912step0 := by apply Matrix.ext; unfold raw42912step1 raw42912step0; decide +kernel
      have hl : raw42912step0Labels = labelEmbedding1 ∘ raw42912step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42912step0 raw42912step0Labels raw42912step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw42913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42913Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42913step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42913 raw42913Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw42913 raw42913Labels = mixedMoment B raw42913step0 raw42913step0Labels := by
      have ha : raw42913step0 = (fun i j => raw42913 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42913step0 raw42913; decide +kernel
      have hl : raw42913step0Labels = raw42913Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42913 raw42913Labels permutation674 permutation5
    mixedMoment B raw42913step0 raw42913step0Labels = mixedMoment B raw42913step1 raw42913step1Labels := by
      have ha : raw42913step1 = raw42913step0 := by apply Matrix.ext; unfold raw42913step1 raw42913step0; decide +kernel
      have hl : raw42913step0Labels = labelEmbedding9 ∘ raw42913step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42913step0 raw42913step0Labels raw42913step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw42914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42914Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42914step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42914step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42914 raw42914Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw42914 raw42914Labels = mixedMoment B raw42914step0 raw42914step0Labels := by
      have ha : raw42914step0 = (fun i j => raw42914 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42914step0 raw42914; decide +kernel
      have hl : raw42914step0Labels = raw42914Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42914 raw42914Labels permutation200 permutation4
    mixedMoment B raw42914step0 raw42914step0Labels = mixedMoment B raw42914step1 raw42914step1Labels := by
      have ha : raw42914step1 = -raw42914step0 := by apply Matrix.ext; change ∀ i j, raw42914step1 i j = -(raw42914step0 i j); unfold raw42914step1 raw42914step0; decide +kernel
      have hl : raw42914step1Labels = raw42914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42914step1 raw42914step1Labels = mixedMoment B raw42914step2 raw42914step2Labels := by
      have ha : raw42914step2 = raw42914step1 := by apply Matrix.ext; unfold raw42914step2 raw42914step1; decide +kernel
      have hl : raw42914step1Labels = labelEmbedding1 ∘ raw42914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42914step1 raw42914step1Labels raw42914step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw42915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42915Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42915step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42915 raw42915Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw42915 raw42915Labels = mixedMoment B raw42915step0 raw42915step0Labels := by
      have ha : raw42915step0 = (fun i j => raw42915 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42915step0 raw42915; decide +kernel
      have hl : raw42915step0Labels = raw42915Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42915 raw42915Labels permutation674 permutation5
    mixedMoment B raw42915step0 raw42915step0Labels = mixedMoment B raw42915step1 raw42915step1Labels := by
      have ha : raw42915step1 = raw42915step0 := by apply Matrix.ext; unfold raw42915step1 raw42915step0; decide +kernel
      have hl : raw42915step0Labels = labelEmbedding9 ∘ raw42915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42915step0 raw42915step0Labels raw42915step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw42916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42916Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42916step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42916step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42916step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42916 raw42916Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw42916 raw42916Labels = mixedMoment B raw42916step0 raw42916step0Labels := by
      have ha : raw42916step0 = (fun i j => raw42916 (permutation201 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42916step0 raw42916; decide +kernel
      have hl : raw42916step0Labels = raw42916Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42916 raw42916Labels permutation201 permutation4
    mixedMoment B raw42916step0 raw42916step0Labels = mixedMoment B raw42916step1 raw42916step1Labels := by
      have ha : raw42916step1 = -raw42916step0 := by apply Matrix.ext; change ∀ i j, raw42916step1 i j = -(raw42916step0 i j); unfold raw42916step1 raw42916step0; decide +kernel
      have hl : raw42916step1Labels = raw42916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42916step1 raw42916step1Labels = mixedMoment B raw42916step2 raw42916step2Labels := by
      have ha : raw42916step2 = raw42916step1 := by apply Matrix.ext; unfold raw42916step2 raw42916step1; decide +kernel
      have hl : raw42916step1Labels = labelEmbedding1 ∘ raw42916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42916step1 raw42916step1Labels raw42916step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3976 node3976Labels := by rfl

def raw42917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42917Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42917step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42917 raw42917Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw42917 raw42917Labels = mixedMoment B raw42917step0 raw42917step0Labels := by
      have ha : raw42917step0 = (fun i j => raw42917 (permutation577 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42917step0 raw42917; decide +kernel
      have hl : raw42917step0Labels = raw42917Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42917 raw42917Labels permutation577 permutation5
    mixedMoment B raw42917step0 raw42917step0Labels = mixedMoment B raw42917step1 raw42917step1Labels := by
      have ha : raw42917step1 = raw42917step0 := by apply Matrix.ext; unfold raw42917step1 raw42917step0; decide +kernel
      have hl : raw42917step0Labels = labelEmbedding9 ∘ raw42917step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42917step0 raw42917step0Labels raw42917step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw42918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42918Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42918step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42918 raw42918Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw42918 raw42918Labels = mixedMoment B raw42918step0 raw42918step0Labels := by
      have ha : raw42918step0 = (fun i j => raw42918 (permutation535 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42918step0 raw42918; decide +kernel
      have hl : raw42918step0Labels = raw42918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42918 raw42918Labels permutation535 permutation4
    mixedMoment B raw42918step0 raw42918step0Labels = mixedMoment B raw42918step1 raw42918step1Labels := by
      have ha : raw42918step1 = raw42918step0 := by apply Matrix.ext; unfold raw42918step1 raw42918step0; decide +kernel
      have hl : raw42918step0Labels = labelEmbedding1 ∘ raw42918step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42918step0 raw42918step0Labels raw42918step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2698 node2698Labels := by rfl

def raw42919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42919Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42919step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42919step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42919step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42919 raw42919Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw42919 raw42919Labels = mixedMoment B raw42919step0 raw42919step0Labels := by
      have ha : raw42919step0 = (fun i j => raw42919 (permutation535 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42919step0 raw42919; decide +kernel
      have hl : raw42919step0Labels = raw42919Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42919 raw42919Labels permutation535 permutation4
    mixedMoment B raw42919step0 raw42919step0Labels = mixedMoment B raw42919step1 raw42919step1Labels := by
      have ha : raw42919step1 = raw42919step0 := by apply Matrix.ext; unfold raw42919step1 raw42919step0; decide +kernel
      have hl : raw42919step0Labels = labelEmbedding10 ∘ raw42919step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42919step0 raw42919step0Labels raw42919step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

def raw42920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42920Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]
def raw42920step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42920step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42920 raw42920Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw42920 raw42920Labels = mixedMoment B raw42920step0 raw42920step0Labels := by
      have hz : ∀ j, raw42920 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42920step0 = (fun i j => raw42920 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42920step0 raw42920; decide +kernel
      have hl : raw42920step0Labels = raw42920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42920 raw42920Labels permutation434 hz
    mixedMoment B raw42920step0 raw42920step0Labels = mixedMoment B raw42920step1 raw42920step1Labels := by
      have ha : raw42920step1 = (fun i j => raw42920step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42920step1 raw42920step0; decide +kernel
      have hl : raw42920step1Labels = raw42920step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42920step0 raw42920step0Labels permutation137 permutation4
    mixedMoment B raw42920step1 raw42920step1Labels = mixedMoment B raw42920step2 raw42920step2Labels := by
      have ha : raw42920step2 = raw42920step1 := by apply Matrix.ext; unfold raw42920step2 raw42920step1; decide +kernel
      have hl : raw42920step1Labels = labelEmbedding1 ∘ raw42920step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42920step1 raw42920step1Labels raw42920step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw42921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42921Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]
def raw42921step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42921step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42921step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42921 raw42921Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw42921 raw42921Labels = mixedMoment B raw42921step0 raw42921step0Labels := by
      have hz : ∀ j, raw42921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42921step0 = (fun i j => raw42921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42921step0 raw42921; decide +kernel
      have hl : raw42921step0Labels = raw42921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42921 raw42921Labels permutation434 hz
    mixedMoment B raw42921step0 raw42921step0Labels = mixedMoment B raw42921step1 raw42921step1Labels := by
      have ha : raw42921step1 = (fun i j => raw42921step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42921step1 raw42921step0; decide +kernel
      have hl : raw42921step1Labels = raw42921step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42921step0 raw42921step0Labels permutation137 permutation5
    mixedMoment B raw42921step1 raw42921step1Labels = mixedMoment B raw42921step2 raw42921step2Labels := by
      have ha : raw42921step2 = raw42921step1 := by apply Matrix.ext; unfold raw42921step2 raw42921step1; decide +kernel
      have hl : raw42921step1Labels = labelEmbedding9 ∘ raw42921step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42921step1 raw42921step1Labels raw42921step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw42922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42922Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw42922step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42922step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42922 raw42922Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw42922 raw42922Labels = mixedMoment B raw42922step0 raw42922step0Labels := by
      have hz : ∀ j, raw42922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42922step0 = (fun i j => raw42922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42922step0 raw42922; decide +kernel
      have hl : raw42922step0Labels = raw42922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42922 raw42922Labels permutation434 hz
    mixedMoment B raw42922step0 raw42922step0Labels = mixedMoment B raw42922step1 raw42922step1Labels := by
      have ha : raw42922step1 = (fun i j => raw42922step0 (permutation113 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42922step1 raw42922step0; decide +kernel
      have hl : raw42922step1Labels = raw42922step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42922step0 raw42922step0Labels permutation113 permutation4
    mixedMoment B raw42922step1 raw42922step1Labels = mixedMoment B raw42922step2 raw42922step2Labels := by
      have ha : raw42922step2 = raw42922step1 := by apply Matrix.ext; unfold raw42922step2 raw42922step1; decide +kernel
      have hl : raw42922step1Labels = labelEmbedding1 ∘ raw42922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42922step1 raw42922step1Labels raw42922step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw42923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42923Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw42923step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42923step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42923step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42923 raw42923Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw42923 raw42923Labels = mixedMoment B raw42923step0 raw42923step0Labels := by
      have hz : ∀ j, raw42923 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42923step0 = (fun i j => raw42923 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42923step0 raw42923; decide +kernel
      have hl : raw42923step0Labels = raw42923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42923 raw42923Labels permutation434 hz
    mixedMoment B raw42923step0 raw42923step0Labels = mixedMoment B raw42923step1 raw42923step1Labels := by
      have ha : raw42923step1 = (fun i j => raw42923step0 (permutation128 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42923step1 raw42923step0; decide +kernel
      have hl : raw42923step1Labels = raw42923step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42923step0 raw42923step0Labels permutation128 permutation7
    mixedMoment B raw42923step1 raw42923step1Labels = mixedMoment B raw42923step2 raw42923step2Labels := by
      have ha : raw42923step2 = raw42923step1 := by apply Matrix.ext; unfold raw42923step2 raw42923step1; decide +kernel
      have hl : raw42923step1Labels = labelEmbedding6 ∘ raw42923step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42923step1 raw42923step1Labels raw42923step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw42924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42924Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42924step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42924step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42924step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42924 raw42924Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw42924 raw42924Labels = mixedMoment B raw42924step0 raw42924step0Labels := by
      have ha : raw42924step0 = (fun i j => raw42924 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42924step0 raw42924; decide +kernel
      have hl : raw42924step0Labels = raw42924Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42924 raw42924Labels permutation224 permutation4
    mixedMoment B raw42924step0 raw42924step0Labels = mixedMoment B raw42924step1 raw42924step1Labels := by
      have ha : raw42924step1 = -raw42924step0 := by apply Matrix.ext; change ∀ i j, raw42924step1 i j = -(raw42924step0 i j); unfold raw42924step1 raw42924step0; decide +kernel
      have hl : raw42924step1Labels = raw42924step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42924step1 raw42924step1Labels = mixedMoment B raw42924step2 raw42924step2Labels := by
      have ha : raw42924step2 = raw42924step1 := by apply Matrix.ext; unfold raw42924step2 raw42924step1; decide +kernel
      have hl : raw42924step1Labels = labelEmbedding1 ∘ raw42924step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42924step1 raw42924step1Labels raw42924step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw42925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42925Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42925step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42925 raw42925Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42925 raw42925Labels = mixedMoment B raw42925step0 raw42925step0Labels := by
      have ha : raw42925step0 = (fun i j => raw42925 (permutation653 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42925step0 raw42925; decide +kernel
      have hl : raw42925step0Labels = raw42925Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42925 raw42925Labels permutation653 permutation5
    mixedMoment B raw42925step0 raw42925step0Labels = mixedMoment B raw42925step1 raw42925step1Labels := by
      have ha : raw42925step1 = raw42925step0 := by apply Matrix.ext; unfold raw42925step1 raw42925step0; decide +kernel
      have hl : raw42925step0Labels = labelEmbedding9 ∘ raw42925step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42925step0 raw42925step0Labels raw42925step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw42926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42926Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42926step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42926step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42926step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42926step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42926 raw42926Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw42926 raw42926Labels = mixedMoment B raw42926step0 raw42926step0Labels := by
      have ha : raw42926step0 = (fun i j => raw42926 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42926step0 raw42926; decide +kernel
      have hl : raw42926step0Labels = raw42926Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42926 raw42926Labels permutation683 permutation2
    mixedMoment B raw42926step0 raw42926step0Labels = mixedMoment B raw42926step1 raw42926step1Labels := by
      have ha : raw42926step1 = -raw42926step0 := by apply Matrix.ext; change ∀ i j, raw42926step1 i j = -(raw42926step0 i j); unfold raw42926step1 raw42926step0; decide +kernel
      have hl : raw42926step1Labels = raw42926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42926step1 raw42926step1Labels = mixedMoment B raw42926step2 raw42926step2Labels := by
      have ha : raw42926step2 = raw42926step1 := by apply Matrix.ext; unfold raw42926step2 raw42926step1; decide +kernel
      have hl : raw42926step1Labels = labelEmbedding1 ∘ raw42926step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42926step1 raw42926step1Labels raw42926step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw42927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42927Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42927step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42927step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42927step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42927 raw42927Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw42927 raw42927Labels = mixedMoment B raw42927step0 raw42927step0Labels := by
      have ha : raw42927step0 = (fun i j => raw42927 (permutation601 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42927step0 raw42927; decide +kernel
      have hl : raw42927step0Labels = raw42927Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42927 raw42927Labels permutation601 permutation7
    mixedMoment B raw42927step0 raw42927step0Labels = mixedMoment B raw42927step1 raw42927step1Labels := by
      have ha : raw42927step1 = raw42927step0 := by apply Matrix.ext; unfold raw42927step1 raw42927step0; decide +kernel
      have hl : raw42927step0Labels = labelEmbedding6 ∘ raw42927step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42927step0 raw42927step0Labels raw42927step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw42928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42928Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42928step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42928step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42928step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42928step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42928step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42928 raw42928Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw42928 raw42928Labels = mixedMoment B raw42928step0 raw42928step0Labels := by
      have ha : raw42928step0 = (fun i j => raw42928 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42928step0 raw42928; decide +kernel
      have hl : raw42928step0Labels = raw42928Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42928 raw42928Labels permutation683 permutation2
    mixedMoment B raw42928step0 raw42928step0Labels = mixedMoment B raw42928step1 raw42928step1Labels := by
      have ha : raw42928step1 = -raw42928step0 := by apply Matrix.ext; change ∀ i j, raw42928step1 i j = -(raw42928step0 i j); unfold raw42928step1 raw42928step0; decide +kernel
      have hl : raw42928step1Labels = raw42928step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42928step1 raw42928step1Labels = mixedMoment B raw42928step2 raw42928step2Labels := by
      have ha : raw42928step2 = raw42928step1 := by apply Matrix.ext; unfold raw42928step2 raw42928step1; decide +kernel
      have hl : raw42928step1Labels = labelEmbedding1 ∘ raw42928step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42928step1 raw42928step1Labels raw42928step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw42929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42929Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42929step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42929 raw42929Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw42929 raw42929Labels = mixedMoment B raw42929step0 raw42929step0Labels := by
      have ha : raw42929step0 = (fun i j => raw42929 (permutation599 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42929step0 raw42929; decide +kernel
      have hl : raw42929step0Labels = raw42929Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42929 raw42929Labels permutation599 permutation7
    mixedMoment B raw42929step0 raw42929step0Labels = mixedMoment B raw42929step1 raw42929step1Labels := by
      have ha : raw42929step1 = raw42929step0 := by apply Matrix.ext; unfold raw42929step1 raw42929step0; decide +kernel
      have hl : raw42929step0Labels = labelEmbedding6 ∘ raw42929step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42929step0 raw42929step0Labels raw42929step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw42930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42930Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42930step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42930step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42930step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42930step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42930 raw42930Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw42930 raw42930Labels = mixedMoment B raw42930step0 raw42930step0Labels := by
      have ha : raw42930step0 = (fun i j => raw42930 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42930step0 raw42930; decide +kernel
      have hl : raw42930step0Labels = raw42930Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42930 raw42930Labels permutation212 permutation4
    mixedMoment B raw42930step0 raw42930step0Labels = mixedMoment B raw42930step1 raw42930step1Labels := by
      have ha : raw42930step1 = -raw42930step0 := by apply Matrix.ext; change ∀ i j, raw42930step1 i j = -(raw42930step0 i j); unfold raw42930step1 raw42930step0; decide +kernel
      have hl : raw42930step1Labels = raw42930step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42930step1 raw42930step1Labels = mixedMoment B raw42930step2 raw42930step2Labels := by
      have ha : raw42930step2 = raw42930step1 := by apply Matrix.ext; unfold raw42930step2 raw42930step1; decide +kernel
      have hl : raw42930step1Labels = labelEmbedding1 ∘ raw42930step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42930step1 raw42930step1Labels raw42930step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw42931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42931Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42931step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42931step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42931step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42931step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42931 raw42931Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42931 raw42931Labels = mixedMoment B raw42931step0 raw42931step0Labels := by
      have ha : raw42931step0 = (fun i j => raw42931 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42931step0 raw42931; decide +kernel
      have hl : raw42931step0Labels = raw42931Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42931 raw42931Labels permutation688 permutation3
    mixedMoment B raw42931step0 raw42931step0Labels = mixedMoment B raw42931step1 raw42931step1Labels := by
      have ha : raw42931step1 = -raw42931step0 := by apply Matrix.ext; change ∀ i j, raw42931step1 i j = -(raw42931step0 i j); unfold raw42931step1 raw42931step0; decide +kernel
      have hl : raw42931step1Labels = raw42931step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42931step1 raw42931step1Labels = mixedMoment B raw42931step2 raw42931step2Labels := by
      have ha : raw42931step2 = raw42931step1 := by apply Matrix.ext; unfold raw42931step2 raw42931step1; decide +kernel
      have hl : raw42931step1Labels = labelEmbedding7 ∘ raw42931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42931step1 raw42931step1Labels raw42931step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw42932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42932Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42932step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42932step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42932step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42932step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42932 raw42932Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw42932 raw42932Labels = mixedMoment B raw42932step0 raw42932step0Labels := by
      have ha : raw42932step0 = (fun i j => raw42932 (permutation205 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42932step0 raw42932; decide +kernel
      have hl : raw42932step0Labels = raw42932Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42932 raw42932Labels permutation205 permutation4
    mixedMoment B raw42932step0 raw42932step0Labels = mixedMoment B raw42932step1 raw42932step1Labels := by
      have ha : raw42932step1 = -raw42932step0 := by apply Matrix.ext; change ∀ i j, raw42932step1 i j = -(raw42932step0 i j); unfold raw42932step1 raw42932step0; decide +kernel
      have hl : raw42932step1Labels = raw42932step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42932step1 raw42932step1Labels = mixedMoment B raw42932step2 raw42932step2Labels := by
      have ha : raw42932step2 = raw42932step1 := by apply Matrix.ext; unfold raw42932step2 raw42932step1; decide +kernel
      have hl : raw42932step1Labels = labelEmbedding1 ∘ raw42932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42932step1 raw42932step1Labels raw42932step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw42933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42933Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42933step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42933step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42933step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42933step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42933 raw42933Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw42933 raw42933Labels = mixedMoment B raw42933step0 raw42933step0Labels := by
      have ha : raw42933step0 = (fun i j => raw42933 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42933step0 raw42933; decide +kernel
      have hl : raw42933step0Labels = raw42933Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42933 raw42933Labels permutation688 permutation3
    mixedMoment B raw42933step0 raw42933step0Labels = mixedMoment B raw42933step1 raw42933step1Labels := by
      have ha : raw42933step1 = -raw42933step0 := by apply Matrix.ext; change ∀ i j, raw42933step1 i j = -(raw42933step0 i j); unfold raw42933step1 raw42933step0; decide +kernel
      have hl : raw42933step1Labels = raw42933step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42933step1 raw42933step1Labels = mixedMoment B raw42933step2 raw42933step2Labels := by
      have ha : raw42933step2 = raw42933step1 := by apply Matrix.ext; unfold raw42933step2 raw42933step1; decide +kernel
      have hl : raw42933step1Labels = labelEmbedding7 ∘ raw42933step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42933step1 raw42933step1Labels raw42933step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw42934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42934Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42934step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42934step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42934step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42934 raw42934Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw42934 raw42934Labels = mixedMoment B raw42934step0 raw42934step0Labels := by
      have ha : raw42934step0 = (fun i j => raw42934 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42934step0 raw42934; decide +kernel
      have hl : raw42934step0Labels = raw42934Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42934 raw42934Labels permutation683 permutation2
    mixedMoment B raw42934step0 raw42934step0Labels = mixedMoment B raw42934step1 raw42934step1Labels := by
      have ha : raw42934step1 = -raw42934step0 := by apply Matrix.ext; change ∀ i j, raw42934step1 i j = -(raw42934step0 i j); unfold raw42934step1 raw42934step0; decide +kernel
      have hl : raw42934step1Labels = raw42934step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42934step1 raw42934step1Labels = mixedMoment B raw42934step2 raw42934step2Labels := by
      have ha : raw42934step2 = raw42934step1 := by apply Matrix.ext; unfold raw42934step2 raw42934step1; decide +kernel
      have hl : raw42934step1Labels = labelEmbedding1 ∘ raw42934step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42934step1 raw42934step1Labels raw42934step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw42935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42935Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42935step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42935 raw42935Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw42935 raw42935Labels = mixedMoment B raw42935step0 raw42935step0Labels := by
      have ha : raw42935step0 = (fun i j => raw42935 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42935step0 raw42935; decide +kernel
      have hl : raw42935step0Labels = raw42935Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42935 raw42935Labels permutation650 permutation7
    mixedMoment B raw42935step0 raw42935step0Labels = mixedMoment B raw42935step1 raw42935step1Labels := by
      have ha : raw42935step1 = raw42935step0 := by apply Matrix.ext; unfold raw42935step1 raw42935step0; decide +kernel
      have hl : raw42935step0Labels = labelEmbedding6 ∘ raw42935step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42935step0 raw42935step0Labels raw42935step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw42936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42936Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42936step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42936step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42936step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42936step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42936step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42936 raw42936Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw42936 raw42936Labels = mixedMoment B raw42936step0 raw42936step0Labels := by
      have hz : ∀ j, raw42936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42936step0 = (fun i j => raw42936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42936step0 raw42936; decide +kernel
      have hl : raw42936step0Labels = raw42936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42936 raw42936Labels permutation434 hz
    mixedMoment B raw42936step0 raw42936step0Labels = mixedMoment B raw42936step1 raw42936step1Labels := by
      have ha : raw42936step1 = (fun i j => raw42936step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42936step1 raw42936step0; decide +kernel
      have hl : raw42936step1Labels = raw42936step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42936step0 raw42936step0Labels permutation44 permutation4
    mixedMoment B raw42936step1 raw42936step1Labels = mixedMoment B raw42936step2 raw42936step2Labels := by
      have ha : raw42936step2 = -raw42936step1 := by apply Matrix.ext; change ∀ i j, raw42936step2 i j = -(raw42936step1 i j); unfold raw42936step2 raw42936step1; decide +kernel
      have hl : raw42936step2Labels = raw42936step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42936step2 raw42936step2Labels = mixedMoment B raw42936step3 raw42936step3Labels := by
      have ha : raw42936step3 = raw42936step2 := by apply Matrix.ext; unfold raw42936step3 raw42936step2; decide +kernel
      have hl : raw42936step2Labels = labelEmbedding1 ∘ raw42936step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42936step2 raw42936step2Labels raw42936step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw42937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42937Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42937step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42937step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42937 raw42937Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42937 raw42937Labels = mixedMoment B raw42937step0 raw42937step0Labels := by
      have hz : ∀ j, raw42937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42937step0 = (fun i j => raw42937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42937step0 raw42937; decide +kernel
      have hl : raw42937step0Labels = raw42937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42937 raw42937Labels permutation434 hz
    mixedMoment B raw42937step0 raw42937step0Labels = mixedMoment B raw42937step1 raw42937step1Labels := by
      have ha : raw42937step1 = (fun i j => raw42937step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42937step1 raw42937step0; decide +kernel
      have hl : raw42937step1Labels = raw42937step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42937step0 raw42937step0Labels permutation143 permutation5
    mixedMoment B raw42937step1 raw42937step1Labels = mixedMoment B raw42937step2 raw42937step2Labels := by
      have ha : raw42937step2 = raw42937step1 := by apply Matrix.ext; unfold raw42937step2 raw42937step1; decide +kernel
      have hl : raw42937step1Labels = labelEmbedding9 ∘ raw42937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42937step1 raw42937step1Labels raw42937step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw42938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42938Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw42938step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42938step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42938step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42938 raw42938Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw42938 raw42938Labels = mixedMoment B raw42938step0 raw42938step0Labels := by
      have hz : ∀ j, raw42938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42938step0 = (fun i j => raw42938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42938step0 raw42938; decide +kernel
      have hl : raw42938step0Labels = raw42938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42938 raw42938Labels permutation434 hz
    mixedMoment B raw42938step0 raw42938step0Labels = mixedMoment B raw42938step1 raw42938step1Labels := by
      have ha : raw42938step1 = (fun i j => raw42938step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42938step1 raw42938step0; decide +kernel
      have hl : raw42938step1Labels = raw42938step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42938step0 raw42938step0Labels permutation146 permutation2
    mixedMoment B raw42938step1 raw42938step1Labels = mixedMoment B raw42938step2 raw42938step2Labels := by
      have ha : raw42938step2 = -raw42938step1 := by apply Matrix.ext; change ∀ i j, raw42938step2 i j = -(raw42938step1 i j); unfold raw42938step2 raw42938step1; decide +kernel
      have hl : raw42938step2Labels = raw42938step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42938step2 raw42938step2Labels = mixedMoment B raw42938step3 raw42938step3Labels := by
      have ha : raw42938step3 = raw42938step2 := by apply Matrix.ext; unfold raw42938step3 raw42938step2; decide +kernel
      have hl : raw42938step2Labels = labelEmbedding1 ∘ raw42938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42938step2 raw42938step2Labels raw42938step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw42939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42939Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw42939step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42939step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42939 raw42939Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw42939 raw42939Labels = mixedMoment B raw42939step0 raw42939step0Labels := by
      have hz : ∀ j, raw42939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42939step0 = (fun i j => raw42939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42939step0 raw42939; decide +kernel
      have hl : raw42939step0Labels = raw42939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42939 raw42939Labels permutation434 hz
    mixedMoment B raw42939step0 raw42939step0Labels = mixedMoment B raw42939step1 raw42939step1Labels := by
      have ha : raw42939step1 = (fun i j => raw42939step0 (permutation132 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42939step1 raw42939step0; decide +kernel
      have hl : raw42939step1Labels = raw42939step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42939step0 raw42939step0Labels permutation132 permutation7
    mixedMoment B raw42939step1 raw42939step1Labels = mixedMoment B raw42939step2 raw42939step2Labels := by
      have ha : raw42939step2 = raw42939step1 := by apply Matrix.ext; unfold raw42939step2 raw42939step1; decide +kernel
      have hl : raw42939step1Labels = labelEmbedding6 ∘ raw42939step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42939step1 raw42939step1Labels raw42939step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw42940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42940Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42940step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42940step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42940 raw42940Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw42940 raw42940Labels = mixedMoment B raw42940step0 raw42940step0Labels := by
      have ha : raw42940step0 = (fun i j => raw42940 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42940step0 raw42940; decide +kernel
      have hl : raw42940step0Labels = raw42940Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42940 raw42940Labels permutation683 permutation2
    mixedMoment B raw42940step0 raw42940step0Labels = mixedMoment B raw42940step1 raw42940step1Labels := by
      have ha : raw42940step1 = -raw42940step0 := by apply Matrix.ext; change ∀ i j, raw42940step1 i j = -(raw42940step0 i j); unfold raw42940step1 raw42940step0; decide +kernel
      have hl : raw42940step1Labels = raw42940step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42940step1 raw42940step1Labels = mixedMoment B raw42940step2 raw42940step2Labels := by
      have ha : raw42940step2 = raw42940step1 := by apply Matrix.ext; unfold raw42940step2 raw42940step1; decide +kernel
      have hl : raw42940step1Labels = labelEmbedding1 ∘ raw42940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42940step1 raw42940step1Labels raw42940step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw42941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42941Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw42941step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw42941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42941 raw42941Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw42941 raw42941Labels = mixedMoment B raw42941step0 raw42941step0Labels := by
      have ha : raw42941step0 = (fun i j => raw42941 (permutation601 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42941step0 raw42941; decide +kernel
      have hl : raw42941step0Labels = raw42941Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42941 raw42941Labels permutation601 permutation7
    mixedMoment B raw42941step0 raw42941step0Labels = mixedMoment B raw42941step1 raw42941step1Labels := by
      have ha : raw42941step1 = raw42941step0 := by apply Matrix.ext; unfold raw42941step1 raw42941step0; decide +kernel
      have hl : raw42941step0Labels = labelEmbedding6 ∘ raw42941step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42941step0 raw42941step0Labels raw42941step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw42942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42942Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42942step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42942step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42942 raw42942Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw42942 raw42942Labels = mixedMoment B raw42942step0 raw42942step0Labels := by
      have ha : raw42942step0 = (fun i j => raw42942 (permutation406 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42942step0 raw42942; decide +kernel
      have hl : raw42942step0Labels = raw42942Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42942 raw42942Labels permutation406 permutation4
    mixedMoment B raw42942step0 raw42942step0Labels = mixedMoment B raw42942step1 raw42942step1Labels := by
      have ha : raw42942step1 = raw42942step0 := by apply Matrix.ext; unfold raw42942step1 raw42942step0; decide +kernel
      have hl : raw42942step0Labels = labelEmbedding1 ∘ raw42942step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42942step0 raw42942step0Labels raw42942step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw42943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42943Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42943step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42943 raw42943Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw42943 raw42943Labels = mixedMoment B raw42943step0 raw42943step0Labels := by
      have ha : raw42943step0 = (fun i j => raw42943 (permutation377 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42943step0 raw42943; decide +kernel
      have hl : raw42943step0Labels = raw42943Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42943 raw42943Labels permutation377 permutation6
    mixedMoment B raw42943step0 raw42943step0Labels = mixedMoment B raw42943step1 raw42943step1Labels := by
      have ha : raw42943step1 = -raw42943step0 := by apply Matrix.ext; change ∀ i j, raw42943step1 i j = -(raw42943step0 i j); unfold raw42943step1 raw42943step0; decide +kernel
      have hl : raw42943step1Labels = raw42943step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw42944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42944Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw42944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42944 raw42944Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw42944 raw42944Labels = mixedMoment B raw42944step0 raw42944step0Labels := by
      have hz : ∀ j, raw42944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42944step0 = (fun i j => raw42944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42944step0 raw42944; decide +kernel
      have hl : raw42944step0Labels = raw42944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42944 raw42944Labels permutation434 hz
    mixedMoment B raw42944step0 raw42944step0Labels = mixedMoment B raw42944step1 raw42944step1Labels := by
      have ha : raw42944step1 = (fun i j => raw42944step0 (permutation95 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42944step1 raw42944step0; decide +kernel
      have hl : raw42944step1Labels = raw42944step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42944step0 raw42944step0Labels permutation95 permutation4
    mixedMoment B raw42944step1 raw42944step1Labels = mixedMoment B raw42944step2 raw42944step2Labels := by
      have ha : raw42944step2 = raw42944step1 := by apply Matrix.ext; unfold raw42944step2 raw42944step1; decide +kernel
      have hl : raw42944step1Labels = labelEmbedding1 ∘ raw42944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42944step1 raw42944step1Labels raw42944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw42945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42945Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw42945step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw42945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42945step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42945 raw42945Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw42945 raw42945Labels = mixedMoment B raw42945step0 raw42945step0Labels := by
      have hz : ∀ j, raw42945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42945step0 = (fun i j => raw42945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42945step0 raw42945; decide +kernel
      have hl : raw42945step0Labels = raw42945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42945 raw42945Labels permutation434 hz
    mixedMoment B raw42945step0 raw42945step0Labels = mixedMoment B raw42945step1 raw42945step1Labels := by
      have ha : raw42945step1 = (fun i j => raw42945step0 (permutation88 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42945step1 raw42945step0; decide +kernel
      have hl : raw42945step1Labels = raw42945step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42945step0 raw42945step0Labels permutation88 permutation6
    mixedMoment B raw42945step1 raw42945step1Labels = mixedMoment B raw42945step2 raw42945step2Labels := by
      have ha : raw42945step2 = -raw42945step1 := by apply Matrix.ext; change ∀ i j, raw42945step2 i j = -(raw42945step1 i j); unfold raw42945step2 raw42945step1; decide +kernel
      have hl : raw42945step2Labels = raw42945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw42946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42946Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw42946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42946 raw42946Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw42946 raw42946Labels = mixedMoment B raw42946step0 raw42946step0Labels := by
      have ha : raw42946step0 = (fun i j => raw42946 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42946step0 raw42946; decide +kernel
      have hl : raw42946step0Labels = raw42946Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42946 raw42946Labels permutation683 permutation2
    mixedMoment B raw42946step0 raw42946step0Labels = mixedMoment B raw42946step1 raw42946step1Labels := by
      have ha : raw42946step1 = -raw42946step0 := by apply Matrix.ext; change ∀ i j, raw42946step1 i j = -(raw42946step0 i j); unfold raw42946step1 raw42946step0; decide +kernel
      have hl : raw42946step1Labels = raw42946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42946step1 raw42946step1Labels = mixedMoment B raw42946step2 raw42946step2Labels := by
      have ha : raw42946step2 = raw42946step1 := by apply Matrix.ext; unfold raw42946step2 raw42946step1; decide +kernel
      have hl : raw42946step1Labels = labelEmbedding1 ∘ raw42946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42946step1 raw42946step1Labels raw42946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

def raw42947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42947Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42947step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42947 raw42947Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw42947 raw42947Labels = mixedMoment B raw42947step0 raw42947step0Labels := by
      have ha : raw42947step0 = (fun i j => raw42947 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42947step0 raw42947; decide +kernel
      have hl : raw42947step0Labels = raw42947Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42947 raw42947Labels permutation650 permutation7
    mixedMoment B raw42947step0 raw42947step0Labels = mixedMoment B raw42947step1 raw42947step1Labels := by
      have ha : raw42947step1 = raw42947step0 := by apply Matrix.ext; unfold raw42947step1 raw42947step0; decide +kernel
      have hl : raw42947step0Labels = labelEmbedding6 ∘ raw42947step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42947step0 raw42947step0Labels raw42947step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5419 node5419Labels := by rfl

def raw42948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42948Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42948step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw42948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42948step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42948step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42948 raw42948Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw42948 raw42948Labels = mixedMoment B raw42948step0 raw42948step0Labels := by
      have hz : ∀ j, raw42948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42948step0 = (fun i j => raw42948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42948step0 raw42948; decide +kernel
      have hl : raw42948step0Labels = raw42948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42948 raw42948Labels permutation434 hz
    mixedMoment B raw42948step0 raw42948step0Labels = mixedMoment B raw42948step1 raw42948step1Labels := by
      have ha : raw42948step1 = (fun i j => raw42948step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42948step1 raw42948step0; decide +kernel
      have hl : raw42948step1Labels = raw42948step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42948step0 raw42948step0Labels permutation146 permutation2
    mixedMoment B raw42948step1 raw42948step1Labels = mixedMoment B raw42948step2 raw42948step2Labels := by
      have ha : raw42948step2 = -raw42948step1 := by apply Matrix.ext; change ∀ i j, raw42948step2 i j = -(raw42948step1 i j); unfold raw42948step2 raw42948step1; decide +kernel
      have hl : raw42948step2Labels = raw42948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42948step2 raw42948step2Labels = mixedMoment B raw42948step3 raw42948step3Labels := by
      have ha : raw42948step3 = raw42948step2 := by apply Matrix.ext; unfold raw42948step3 raw42948step2; decide +kernel
      have hl : raw42948step2Labels = labelEmbedding1 ∘ raw42948step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42948step2 raw42948step2Labels raw42948step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

def raw42949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42949Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42949step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42949step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42949step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42949 raw42949Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw42949 raw42949Labels = mixedMoment B raw42949step0 raw42949step0Labels := by
      have hz : ∀ j, raw42949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42949step0 = (fun i j => raw42949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42949step0 raw42949; decide +kernel
      have hl : raw42949step0Labels = raw42949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42949 raw42949Labels permutation434 hz
    mixedMoment B raw42949step0 raw42949step0Labels = mixedMoment B raw42949step1 raw42949step1Labels := by
      have ha : raw42949step1 = (fun i j => raw42949step0 (permutation132 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42949step1 raw42949step0; decide +kernel
      have hl : raw42949step1Labels = raw42949step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42949step0 raw42949step0Labels permutation132 permutation7
    mixedMoment B raw42949step1 raw42949step1Labels = mixedMoment B raw42949step2 raw42949step2Labels := by
      have ha : raw42949step2 = raw42949step1 := by apply Matrix.ext; unfold raw42949step2 raw42949step1; decide +kernel
      have hl : raw42949step1Labels = labelEmbedding6 ∘ raw42949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42949step1 raw42949step1Labels raw42949step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw42950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42950Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw42950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42950step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw42950step2Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42950step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw42950step3Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42950step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw42950step4Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42950step5 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw42950step5Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical42950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42950 raw42950Labels = mixedMoment B node0 node0Labels := by
  calc
    mixedMoment B raw42950 raw42950Labels = mixedMoment B raw42950step0 raw42950step0Labels := by
      have hz : ∀ j, raw42950 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42950step0 = (fun i j => raw42950 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42950step0 raw42950; decide +kernel
      have hl : raw42950step0Labels = raw42950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42950 raw42950Labels permutation520 hz
    mixedMoment B raw42950step0 raw42950step0Labels = mixedMoment B raw42950step1 raw42950step1Labels := by
      have hz : ∀ j, raw42950step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42950step1 = (fun i j => raw42950step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42950step1 raw42950step0; decide +kernel
      have hl : raw42950step1Labels = raw42950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42950step0 raw42950step0Labels permutation104 hz
    mixedMoment B raw42950step1 raw42950step1Labels = mixedMoment B raw42950step2 raw42950step2Labels := by
      have hz : ∀ i, raw42950step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42950step2 = (fun i j => raw42950step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42950step2 raw42950step1; decide +kernel
      have hl : raw42950step2Labels = (fun j => raw42950step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42950step1 raw42950step1Labels permutation6 hz
    mixedMoment B raw42950step2 raw42950step2Labels = mixedMoment B raw42950step3 raw42950step3Labels := by
      have ha : raw42950step3 = (fun i j => raw42950step2 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw42950step3 raw42950step2; decide +kernel
      have hl : raw42950step3Labels = raw42950step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42950step2 raw42950step2Labels permutation26 permutation0
    mixedMoment B raw42950step3 raw42950step3Labels = mixedMoment B raw42950step4 raw42950step4Labels := by
      have ha : raw42950step4 = -raw42950step3 := by apply Matrix.ext; change ∀ i j, raw42950step4 i j = -(raw42950step3 i j); unfold raw42950step4 raw42950step3; decide +kernel
      have hl : raw42950step4Labels = raw42950step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42950step4 raw42950step4Labels = mixedMoment B raw42950step5 raw42950step5Labels := by
      have ha : raw42950step5 = raw42950step4 := by apply Matrix.ext; unfold raw42950step5 raw42950step4; decide +kernel
      have hl : raw42950step4Labels = labelEmbedding0 ∘ raw42950step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42950step4 raw42950step4Labels raw42950step5Labels labelEmbedding0 hl
    _ = mixedMoment B node0 node0Labels := by rfl

def raw42951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42951Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42951step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw42951step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42951step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw42951step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42951step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw42951step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42951step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw42951step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42951step5 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw42951step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical42951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42951 raw42951Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw42951 raw42951Labels = mixedMoment B raw42951step0 raw42951step0Labels := by
      have hz : ∀ j, raw42951 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42951step0 = (fun i j => raw42951 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42951step0 raw42951; decide +kernel
      have hl : raw42951step0Labels = raw42951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42951 raw42951Labels permutation520 hz
    mixedMoment B raw42951step0 raw42951step0Labels = mixedMoment B raw42951step1 raw42951step1Labels := by
      have hz : ∀ j, raw42951step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42951step1 = (fun i j => raw42951step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42951step1 raw42951step0; decide +kernel
      have hl : raw42951step1Labels = raw42951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42951step0 raw42951step0Labels permutation104 hz
    mixedMoment B raw42951step1 raw42951step1Labels = mixedMoment B raw42951step2 raw42951step2Labels := by
      have hz : ∀ i, raw42951step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42951step2 = (fun i j => raw42951step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42951step2 raw42951step1; decide +kernel
      have hl : raw42951step2Labels = (fun j => raw42951step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42951step1 raw42951step1Labels permutation6 hz
    mixedMoment B raw42951step2 raw42951step2Labels = mixedMoment B raw42951step3 raw42951step3Labels := by
      have ha : raw42951step3 = (fun i j => raw42951step2 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw42951step3 raw42951step2; decide +kernel
      have hl : raw42951step3Labels = raw42951step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42951step2 raw42951step2Labels permutation26 permutation0
    mixedMoment B raw42951step3 raw42951step3Labels = mixedMoment B raw42951step4 raw42951step4Labels := by
      have ha : raw42951step4 = -raw42951step3 := by apply Matrix.ext; change ∀ i j, raw42951step4 i j = -(raw42951step3 i j); unfold raw42951step4 raw42951step3; decide +kernel
      have hl : raw42951step4Labels = raw42951step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42951step4 raw42951step4Labels = mixedMoment B raw42951step5 raw42951step5Labels := by
      have ha : raw42951step5 = raw42951step4 := by apply Matrix.ext; unfold raw42951step5 raw42951step4; decide +kernel
      have hl : raw42951step4Labels = labelEmbedding3 ∘ raw42951step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42951step4 raw42951step4Labels raw42951step5Labels labelEmbedding3 hl
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw42952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42952Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42952 raw42952Labels = mixedMoment B node3111 node3111Labels := by
  calc
    mixedMoment B raw42952 raw42952Labels = mixedMoment B raw42952step0 raw42952step0Labels := by
      have hz : ∀ j, raw42952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42952step0 = (fun i j => raw42952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42952step0 raw42952; decide +kernel
      have hl : raw42952step0Labels = raw42952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42952 raw42952Labels permutation434 hz
    mixedMoment B raw42952step0 raw42952step0Labels = mixedMoment B raw42952step1 raw42952step1Labels := by
      have ha : raw42952step1 = (fun i j => raw42952step0 (permutation146 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42952step1 raw42952step0; decide +kernel
      have hl : raw42952step1Labels = raw42952step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42952step0 raw42952step0Labels permutation146 permutation4
    mixedMoment B raw42952step1 raw42952step1Labels = mixedMoment B raw42952step2 raw42952step2Labels := by
      have ha : raw42952step2 = raw42952step1 := by apply Matrix.ext; unfold raw42952step2 raw42952step1; decide +kernel
      have hl : raw42952step1Labels = labelEmbedding1 ∘ raw42952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42952step1 raw42952step1Labels raw42952step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3111 node3111Labels := by rfl

def raw42953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42953Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42953step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42953step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42953 raw42953Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw42953 raw42953Labels = mixedMoment B raw42953step0 raw42953step0Labels := by
      have hz : ∀ j, raw42953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42953step0 = (fun i j => raw42953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42953step0 raw42953; decide +kernel
      have hl : raw42953step0Labels = raw42953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42953 raw42953Labels permutation434 hz
    mixedMoment B raw42953step0 raw42953step0Labels = mixedMoment B raw42953step1 raw42953step1Labels := by
      have ha : raw42953step1 = (fun i j => raw42953step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42953step1 raw42953step0; decide +kernel
      have hl : raw42953step1Labels = raw42953step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42953step0 raw42953step0Labels permutation146 permutation5
    mixedMoment B raw42953step1 raw42953step1Labels = mixedMoment B raw42953step2 raw42953step2Labels := by
      have ha : raw42953step2 = raw42953step1 := by apply Matrix.ext; unfold raw42953step2 raw42953step1; decide +kernel
      have hl : raw42953step1Labels = labelEmbedding9 ∘ raw42953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42953step1 raw42953step1Labels raw42953step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw42954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42954Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42954step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw42954step1Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42954step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw42954step2Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42954step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42954step3Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42954step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42954step4Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical42954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42954 raw42954Labels = mixedMoment B node3 node3Labels := by
  calc
    mixedMoment B raw42954 raw42954Labels = mixedMoment B raw42954step0 raw42954step0Labels := by
      have hz : ∀ j, raw42954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42954step0 = (fun i j => raw42954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42954step0 raw42954; decide +kernel
      have hl : raw42954step0Labels = raw42954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42954 raw42954Labels permutation434 hz
    mixedMoment B raw42954step0 raw42954step0Labels = mixedMoment B raw42954step1 raw42954step1Labels := by
      have hz : ∀ i, raw42954step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42954step1 = (fun i j => raw42954step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42954step1 raw42954step0; decide +kernel
      have hl : raw42954step1Labels = (fun j => raw42954step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42954step0 raw42954step0Labels permutation6 hz
    mixedMoment B raw42954step1 raw42954step1Labels = mixedMoment B raw42954step2 raw42954step2Labels := by
      have ha : raw42954step2 = (fun i j => raw42954step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw42954step2 raw42954step1; decide +kernel
      have hl : raw42954step2Labels = raw42954step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42954step1 raw42954step1Labels permutation146 permutation0
    mixedMoment B raw42954step2 raw42954step2Labels = mixedMoment B raw42954step3 raw42954step3Labels := by
      have ha : raw42954step3 = -raw42954step2 := by apply Matrix.ext; change ∀ i j, raw42954step3 i j = -(raw42954step2 i j); unfold raw42954step3 raw42954step2; decide +kernel
      have hl : raw42954step3Labels = raw42954step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42954step3 raw42954step3Labels = mixedMoment B raw42954step4 raw42954step4Labels := by
      have ha : raw42954step4 = raw42954step3 := by apply Matrix.ext; unfold raw42954step4 raw42954step3; decide +kernel
      have hl : raw42954step3Labels = labelEmbedding0 ∘ raw42954step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42954step3 raw42954step3Labels raw42954step4Labels labelEmbedding0 hl
    _ = mixedMoment B node3 node3Labels := by rfl

def raw42955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42955Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42955step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42955step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw42955step1Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42955step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw42955step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42955step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42955step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42955step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42955step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical42955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42955 raw42955Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw42955 raw42955Labels = mixedMoment B raw42955step0 raw42955step0Labels := by
      have hz : ∀ j, raw42955 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42955step0 = (fun i j => raw42955 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42955step0 raw42955; decide +kernel
      have hl : raw42955step0Labels = raw42955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42955 raw42955Labels permutation434 hz
    mixedMoment B raw42955step0 raw42955step0Labels = mixedMoment B raw42955step1 raw42955step1Labels := by
      have hz : ∀ i, raw42955step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42955step1 = (fun i j => raw42955step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42955step1 raw42955step0; decide +kernel
      have hl : raw42955step1Labels = (fun j => raw42955step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42955step0 raw42955step0Labels permutation6 hz
    mixedMoment B raw42955step1 raw42955step1Labels = mixedMoment B raw42955step2 raw42955step2Labels := by
      have ha : raw42955step2 = (fun i j => raw42955step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw42955step2 raw42955step1; decide +kernel
      have hl : raw42955step2Labels = raw42955step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42955step1 raw42955step1Labels permutation146 permutation0
    mixedMoment B raw42955step2 raw42955step2Labels = mixedMoment B raw42955step3 raw42955step3Labels := by
      have ha : raw42955step3 = -raw42955step2 := by apply Matrix.ext; change ∀ i j, raw42955step3 i j = -(raw42955step2 i j); unfold raw42955step3 raw42955step2; decide +kernel
      have hl : raw42955step3Labels = raw42955step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42955step3 raw42955step3Labels = mixedMoment B raw42955step4 raw42955step4Labels := by
      have ha : raw42955step4 = raw42955step3 := by apply Matrix.ext; unfold raw42955step4 raw42955step3; decide +kernel
      have hl : raw42955step3Labels = labelEmbedding3 ∘ raw42955step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42955step3 raw42955step3Labels raw42955step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw42956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42956Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42956step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42956step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42956 raw42956Labels = mixedMoment B node4034 node4034Labels := by
  calc
    mixedMoment B raw42956 raw42956Labels = mixedMoment B raw42956step0 raw42956step0Labels := by
      have ha : raw42956step0 = (fun i j => raw42956 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42956step0 raw42956; decide +kernel
      have hl : raw42956step0Labels = raw42956Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42956 raw42956Labels permutation683 permutation2
    mixedMoment B raw42956step0 raw42956step0Labels = mixedMoment B raw42956step1 raw42956step1Labels := by
      have ha : raw42956step1 = -raw42956step0 := by apply Matrix.ext; change ∀ i j, raw42956step1 i j = -(raw42956step0 i j); unfold raw42956step1 raw42956step0; decide +kernel
      have hl : raw42956step1Labels = raw42956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42956step1 raw42956step1Labels = mixedMoment B raw42956step2 raw42956step2Labels := by
      have ha : raw42956step2 = raw42956step1 := by apply Matrix.ext; unfold raw42956step2 raw42956step1; decide +kernel
      have hl : raw42956step1Labels = labelEmbedding1 ∘ raw42956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42956step1 raw42956step1Labels raw42956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4034 node4034Labels := by rfl

def raw42957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42957Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42957step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42957step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42957 raw42957Labels = mixedMoment B node5427 node5427Labels := by
  calc
    mixedMoment B raw42957 raw42957Labels = mixedMoment B raw42957step0 raw42957step0Labels := by
      have ha : raw42957step0 = (fun i j => raw42957 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42957step0 raw42957; decide +kernel
      have hl : raw42957step0Labels = raw42957Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42957 raw42957Labels permutation683 permutation3
    mixedMoment B raw42957step0 raw42957step0Labels = mixedMoment B raw42957step1 raw42957step1Labels := by
      have ha : raw42957step1 = -raw42957step0 := by apply Matrix.ext; change ∀ i j, raw42957step1 i j = -(raw42957step0 i j); unfold raw42957step1 raw42957step0; decide +kernel
      have hl : raw42957step1Labels = raw42957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42957step1 raw42957step1Labels = mixedMoment B raw42957step2 raw42957step2Labels := by
      have ha : raw42957step2 = raw42957step1 := by apply Matrix.ext; unfold raw42957step2 raw42957step1; decide +kernel
      have hl : raw42957step1Labels = labelEmbedding7 ∘ raw42957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42957step1 raw42957step1Labels raw42957step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5427 node5427Labels := by rfl

def raw42958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42958Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42958step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42958 raw42958Labels = mixedMoment B node3855 node3855Labels := by
  calc
    mixedMoment B raw42958 raw42958Labels = mixedMoment B raw42958step0 raw42958step0Labels := by
      have ha : raw42958step0 = (fun i j => raw42958 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42958step0 raw42958; decide +kernel
      have hl : raw42958step0Labels = raw42958Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42958 raw42958Labels permutation683 permutation2
    mixedMoment B raw42958step0 raw42958step0Labels = mixedMoment B raw42958step1 raw42958step1Labels := by
      have ha : raw42958step1 = -raw42958step0 := by apply Matrix.ext; change ∀ i j, raw42958step1 i j = -(raw42958step0 i j); unfold raw42958step1 raw42958step0; decide +kernel
      have hl : raw42958step1Labels = raw42958step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42958step1 raw42958step1Labels = mixedMoment B raw42958step2 raw42958step2Labels := by
      have ha : raw42958step2 = raw42958step1 := by apply Matrix.ext; unfold raw42958step2 raw42958step1; decide +kernel
      have hl : raw42958step1Labels = labelEmbedding1 ∘ raw42958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42958step1 raw42958step1Labels raw42958step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3855 node3855Labels := by rfl

def raw42959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42959Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42959step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42959step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42959step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42959 raw42959Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw42959 raw42959Labels = mixedMoment B raw42959step0 raw42959step0Labels := by
      have ha : raw42959step0 = (fun i j => raw42959 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42959step0 raw42959; decide +kernel
      have hl : raw42959step0Labels = raw42959Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42959 raw42959Labels permutation683 permutation2
    mixedMoment B raw42959step0 raw42959step0Labels = mixedMoment B raw42959step1 raw42959step1Labels := by
      have ha : raw42959step1 = -raw42959step0 := by apply Matrix.ext; change ∀ i j, raw42959step1 i j = -(raw42959step0 i j); unfold raw42959step1 raw42959step0; decide +kernel
      have hl : raw42959step1Labels = raw42959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42959step1 raw42959step1Labels = mixedMoment B raw42959step2 raw42959step2Labels := by
      have ha : raw42959step2 = raw42959step1 := by apply Matrix.ext; unfold raw42959step2 raw42959step1; decide +kernel
      have hl : raw42959step1Labels = labelEmbedding8 ∘ raw42959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42959step1 raw42959step1Labels raw42959step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw42960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42960Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw42960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42960step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42960step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42960 raw42960Labels = mixedMoment B node3228 node3228Labels := by
  calc
    mixedMoment B raw42960 raw42960Labels = mixedMoment B raw42960step0 raw42960step0Labels := by
      have hz : ∀ j, raw42960 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42960step0 = (fun i j => raw42960 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42960step0 raw42960; decide +kernel
      have hl : raw42960step0Labels = raw42960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42960 raw42960Labels permutation520 hz
    mixedMoment B raw42960step0 raw42960step0Labels = mixedMoment B raw42960step1 raw42960step1Labels := by
      have ha : raw42960step1 = (fun i j => raw42960step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42960step1 raw42960step0; decide +kernel
      have hl : raw42960step1Labels = raw42960step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42960step0 raw42960step0Labels permutation146 permutation2
    mixedMoment B raw42960step1 raw42960step1Labels = mixedMoment B raw42960step2 raw42960step2Labels := by
      have ha : raw42960step2 = -raw42960step1 := by apply Matrix.ext; change ∀ i j, raw42960step2 i j = -(raw42960step1 i j); unfold raw42960step2 raw42960step1; decide +kernel
      have hl : raw42960step2Labels = raw42960step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42960step2 raw42960step2Labels = mixedMoment B raw42960step3 raw42960step3Labels := by
      have ha : raw42960step3 = raw42960step2 := by apply Matrix.ext; unfold raw42960step3 raw42960step2; decide +kernel
      have hl : raw42960step2Labels = labelEmbedding1 ∘ raw42960step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42960step2 raw42960step2Labels raw42960step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3228 node3228Labels := by rfl

def raw42961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42961Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw42961step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42961step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42961step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42961step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42961step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42961 raw42961Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw42961 raw42961Labels = mixedMoment B raw42961step0 raw42961step0Labels := by
      have hz : ∀ j, raw42961 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42961step0 = (fun i j => raw42961 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42961step0 raw42961; decide +kernel
      have hl : raw42961step0Labels = raw42961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42961 raw42961Labels permutation520 hz
    mixedMoment B raw42961step0 raw42961step0Labels = mixedMoment B raw42961step1 raw42961step1Labels := by
      have ha : raw42961step1 = (fun i j => raw42961step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42961step1 raw42961step0; decide +kernel
      have hl : raw42961step1Labels = raw42961step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42961step0 raw42961step0Labels permutation150 permutation3
    mixedMoment B raw42961step1 raw42961step1Labels = mixedMoment B raw42961step2 raw42961step2Labels := by
      have ha : raw42961step2 = -raw42961step1 := by apply Matrix.ext; change ∀ i j, raw42961step2 i j = -(raw42961step1 i j); unfold raw42961step2 raw42961step1; decide +kernel
      have hl : raw42961step2Labels = raw42961step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42961step2 raw42961step2Labels = mixedMoment B raw42961step3 raw42961step3Labels := by
      have ha : raw42961step3 = raw42961step2 := by apply Matrix.ext; unfold raw42961step3 raw42961step2; decide +kernel
      have hl : raw42961step2Labels = labelEmbedding7 ∘ raw42961step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42961step2 raw42961step2Labels raw42961step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw42962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42962Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42962step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42962 raw42962Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw42962 raw42962Labels = mixedMoment B raw42962step0 raw42962step0Labels := by
      have ha : raw42962step0 = (fun i j => raw42962 (permutation641 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42962step0 raw42962; decide +kernel
      have hl : raw42962step0Labels = raw42962Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42962 raw42962Labels permutation641 permutation4
    mixedMoment B raw42962step0 raw42962step0Labels = mixedMoment B raw42962step1 raw42962step1Labels := by
      have ha : raw42962step1 = raw42962step0 := by apply Matrix.ext; unfold raw42962step1 raw42962step0; decide +kernel
      have hl : raw42962step0Labels = labelEmbedding1 ∘ raw42962step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42962step0 raw42962step0Labels raw42962step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw42963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42963Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42963step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42963step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42963step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42963 raw42963Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw42963 raw42963Labels = mixedMoment B raw42963step0 raw42963step0Labels := by
      have ha : raw42963step0 = (fun i j => raw42963 (permutation681 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42963step0 raw42963; decide +kernel
      have hl : raw42963step0Labels = raw42963Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42963 raw42963Labels permutation681 permutation5
    mixedMoment B raw42963step0 raw42963step0Labels = mixedMoment B raw42963step1 raw42963step1Labels := by
      have ha : raw42963step1 = raw42963step0 := by apply Matrix.ext; unfold raw42963step1 raw42963step0; decide +kernel
      have hl : raw42963step0Labels = labelEmbedding9 ∘ raw42963step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42963step0 raw42963step0Labels raw42963step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw42964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42964Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42964step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42964 raw42964Labels = mixedMoment B node4038 node4038Labels := by
  calc
    mixedMoment B raw42964 raw42964Labels = mixedMoment B raw42964step0 raw42964step0Labels := by
      have ha : raw42964step0 = (fun i j => raw42964 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42964step0 raw42964; decide +kernel
      have hl : raw42964step0Labels = raw42964Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42964 raw42964Labels permutation683 permutation2
    mixedMoment B raw42964step0 raw42964step0Labels = mixedMoment B raw42964step1 raw42964step1Labels := by
      have ha : raw42964step1 = -raw42964step0 := by apply Matrix.ext; change ∀ i j, raw42964step1 i j = -(raw42964step0 i j); unfold raw42964step1 raw42964step0; decide +kernel
      have hl : raw42964step1Labels = raw42964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42964step1 raw42964step1Labels = mixedMoment B raw42964step2 raw42964step2Labels := by
      have ha : raw42964step2 = raw42964step1 := by apply Matrix.ext; unfold raw42964step2 raw42964step1; decide +kernel
      have hl : raw42964step1Labels = labelEmbedding1 ∘ raw42964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42964step1 raw42964step1Labels raw42964step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4038 node4038Labels := by rfl

def raw42965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42965Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42965step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42965step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42965step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42965step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42965 raw42965Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw42965 raw42965Labels = mixedMoment B raw42965step0 raw42965step0Labels := by
      have ha : raw42965step0 = (fun i j => raw42965 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42965step0 raw42965; decide +kernel
      have hl : raw42965step0Labels = raw42965Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42965 raw42965Labels permutation687 permutation3
    mixedMoment B raw42965step0 raw42965step0Labels = mixedMoment B raw42965step1 raw42965step1Labels := by
      have ha : raw42965step1 = -raw42965step0 := by apply Matrix.ext; change ∀ i j, raw42965step1 i j = -(raw42965step0 i j); unfold raw42965step1 raw42965step0; decide +kernel
      have hl : raw42965step1Labels = raw42965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42965step1 raw42965step1Labels = mixedMoment B raw42965step2 raw42965step2Labels := by
      have ha : raw42965step2 = raw42965step1 := by apply Matrix.ext; unfold raw42965step2 raw42965step1; decide +kernel
      have hl : raw42965step1Labels = labelEmbedding7 ∘ raw42965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42965step1 raw42965step1Labels raw42965step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw42966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42966Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]
def raw42966step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42966step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42966 raw42966Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw42966 raw42966Labels = mixedMoment B raw42966step0 raw42966step0Labels := by
      have hz : ∀ j, raw42966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42966step0 = (fun i j => raw42966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42966step0 raw42966; decide +kernel
      have hl : raw42966step0Labels = raw42966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42966 raw42966Labels permutation434 hz
    mixedMoment B raw42966step0 raw42966step0Labels = mixedMoment B raw42966step1 raw42966step1Labels := by
      have ha : raw42966step1 = (fun i j => raw42966step0 (permutation140 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42966step1 raw42966step0; decide +kernel
      have hl : raw42966step1Labels = raw42966step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42966step0 raw42966step0Labels permutation140 permutation4
    mixedMoment B raw42966step1 raw42966step1Labels = mixedMoment B raw42966step2 raw42966step2Labels := by
      have ha : raw42966step2 = raw42966step1 := by apply Matrix.ext; unfold raw42966step2 raw42966step1; decide +kernel
      have hl : raw42966step1Labels = labelEmbedding1 ∘ raw42966step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42966step1 raw42966step1Labels raw42966step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw42967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42967Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]
def raw42967step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42967step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42967step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42967 raw42967Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw42967 raw42967Labels = mixedMoment B raw42967step0 raw42967step0Labels := by
      have hz : ∀ j, raw42967 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42967step0 = (fun i j => raw42967 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42967step0 raw42967; decide +kernel
      have hl : raw42967step0Labels = raw42967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42967 raw42967Labels permutation434 hz
    mixedMoment B raw42967step0 raw42967step0Labels = mixedMoment B raw42967step1 raw42967step1Labels := by
      have ha : raw42967step1 = (fun i j => raw42967step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42967step1 raw42967step0; decide +kernel
      have hl : raw42967step1Labels = raw42967step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42967step0 raw42967step0Labels permutation144 permutation5
    mixedMoment B raw42967step1 raw42967step1Labels = mixedMoment B raw42967step2 raw42967step2Labels := by
      have ha : raw42967step2 = raw42967step1 := by apply Matrix.ext; unfold raw42967step2 raw42967step1; decide +kernel
      have hl : raw42967step1Labels = labelEmbedding9 ∘ raw42967step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42967step1 raw42967step1Labels raw42967step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw42968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42968Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42968step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42968step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42968step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42968 raw42968Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw42968 raw42968Labels = mixedMoment B raw42968step0 raw42968step0Labels := by
      have ha : raw42968step0 = (fun i j => raw42968 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42968step0 raw42968; decide +kernel
      have hl : raw42968step0Labels = raw42968Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42968 raw42968Labels permutation683 permutation2
    mixedMoment B raw42968step0 raw42968step0Labels = mixedMoment B raw42968step1 raw42968step1Labels := by
      have ha : raw42968step1 = -raw42968step0 := by apply Matrix.ext; change ∀ i j, raw42968step1 i j = -(raw42968step0 i j); unfold raw42968step1 raw42968step0; decide +kernel
      have hl : raw42968step1Labels = raw42968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42968step1 raw42968step1Labels = mixedMoment B raw42968step2 raw42968step2Labels := by
      have ha : raw42968step2 = raw42968step1 := by apply Matrix.ext; unfold raw42968step2 raw42968step1; decide +kernel
      have hl : raw42968step1Labels = labelEmbedding1 ∘ raw42968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42968step1 raw42968step1Labels raw42968step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw42969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42969Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42969step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42969step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42969 raw42969Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw42969 raw42969Labels = mixedMoment B raw42969step0 raw42969step0Labels := by
      have ha : raw42969step0 = (fun i j => raw42969 (permutation657 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42969step0 raw42969; decide +kernel
      have hl : raw42969step0Labels = raw42969Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42969 raw42969Labels permutation657 permutation5
    mixedMoment B raw42969step0 raw42969step0Labels = mixedMoment B raw42969step1 raw42969step1Labels := by
      have ha : raw42969step1 = raw42969step0 := by apply Matrix.ext; unfold raw42969step1 raw42969step0; decide +kernel
      have hl : raw42969step0Labels = labelEmbedding9 ∘ raw42969step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42969step0 raw42969step0Labels raw42969step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw42970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42970Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42970step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42970step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42970step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42970 raw42970Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw42970 raw42970Labels = mixedMoment B raw42970step0 raw42970step0Labels := by
      have ha : raw42970step0 = (fun i j => raw42970 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42970step0 raw42970; decide +kernel
      have hl : raw42970step0Labels = raw42970Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42970 raw42970Labels permutation683 permutation2
    mixedMoment B raw42970step0 raw42970step0Labels = mixedMoment B raw42970step1 raw42970step1Labels := by
      have ha : raw42970step1 = -raw42970step0 := by apply Matrix.ext; change ∀ i j, raw42970step1 i j = -(raw42970step0 i j); unfold raw42970step1 raw42970step0; decide +kernel
      have hl : raw42970step1Labels = raw42970step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42970step1 raw42970step1Labels = mixedMoment B raw42970step2 raw42970step2Labels := by
      have ha : raw42970step2 = raw42970step1 := by apply Matrix.ext; unfold raw42970step2 raw42970step1; decide +kernel
      have hl : raw42970step1Labels = labelEmbedding1 ∘ raw42970step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42970step1 raw42970step1Labels raw42970step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw42971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42971Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42971step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42971 raw42971Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42971 raw42971Labels = mixedMoment B raw42971step0 raw42971step0Labels := by
      have ha : raw42971step0 = (fun i j => raw42971 (permutation665 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42971step0 raw42971; decide +kernel
      have hl : raw42971step0Labels = raw42971Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42971 raw42971Labels permutation665 permutation7
    mixedMoment B raw42971step0 raw42971step0Labels = mixedMoment B raw42971step1 raw42971step1Labels := by
      have ha : raw42971step1 = raw42971step0 := by apply Matrix.ext; unfold raw42971step1 raw42971step0; decide +kernel
      have hl : raw42971step0Labels = labelEmbedding6 ∘ raw42971step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42971step0 raw42971step0Labels raw42971step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw42972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42972Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42972step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42972 raw42972Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw42972 raw42972Labels = mixedMoment B raw42972step0 raw42972step0Labels := by
      have ha : raw42972step0 = (fun i j => raw42972 (permutation641 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42972step0 raw42972; decide +kernel
      have hl : raw42972step0Labels = raw42972Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42972 raw42972Labels permutation641 permutation4
    mixedMoment B raw42972step0 raw42972step0Labels = mixedMoment B raw42972step1 raw42972step1Labels := by
      have ha : raw42972step1 = raw42972step0 := by apply Matrix.ext; unfold raw42972step1 raw42972step0; decide +kernel
      have hl : raw42972step0Labels = labelEmbedding1 ∘ raw42972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42972step0 raw42972step0Labels raw42972step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw42973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42973Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42973step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42973step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42973step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42973step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42973 raw42973Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw42973 raw42973Labels = mixedMoment B raw42973step0 raw42973step0Labels := by
      have ha : raw42973step0 = (fun i j => raw42973 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42973step0 raw42973; decide +kernel
      have hl : raw42973step0Labels = raw42973Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42973 raw42973Labels permutation687 permutation3
    mixedMoment B raw42973step0 raw42973step0Labels = mixedMoment B raw42973step1 raw42973step1Labels := by
      have ha : raw42973step1 = -raw42973step0 := by apply Matrix.ext; change ∀ i j, raw42973step1 i j = -(raw42973step0 i j); unfold raw42973step1 raw42973step0; decide +kernel
      have hl : raw42973step1Labels = raw42973step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42973step1 raw42973step1Labels = mixedMoment B raw42973step2 raw42973step2Labels := by
      have ha : raw42973step2 = raw42973step1 := by apply Matrix.ext; unfold raw42973step2 raw42973step1; decide +kernel
      have hl : raw42973step1Labels = labelEmbedding7 ∘ raw42973step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42973step1 raw42973step1Labels raw42973step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw42974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42974Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42974step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42974step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42974step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42974step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42974 raw42974Labels = mixedMoment B node4028 node4028Labels := by
  calc
    mixedMoment B raw42974 raw42974Labels = mixedMoment B raw42974step0 raw42974step0Labels := by
      have hz : ∀ j, raw42974 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42974step0 = (fun i j => raw42974 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42974step0 raw42974; decide +kernel
      have hl : raw42974step0Labels = raw42974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42974 raw42974Labels permutation434 hz
    mixedMoment B raw42974step0 raw42974step0Labels = mixedMoment B raw42974step1 raw42974step1Labels := by
      have ha : raw42974step1 = (fun i j => raw42974step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42974step1 raw42974step0; decide +kernel
      have hl : raw42974step1Labels = raw42974step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42974step0 raw42974step0Labels permutation146 permutation2
    mixedMoment B raw42974step1 raw42974step1Labels = mixedMoment B raw42974step2 raw42974step2Labels := by
      have ha : raw42974step2 = -raw42974step1 := by apply Matrix.ext; change ∀ i j, raw42974step2 i j = -(raw42974step1 i j); unfold raw42974step2 raw42974step1; decide +kernel
      have hl : raw42974step2Labels = raw42974step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42974step2 raw42974step2Labels = mixedMoment B raw42974step3 raw42974step3Labels := by
      have ha : raw42974step3 = raw42974step2 := by apply Matrix.ext; unfold raw42974step3 raw42974step2; decide +kernel
      have hl : raw42974step2Labels = labelEmbedding1 ∘ raw42974step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42974step2 raw42974step2Labels raw42974step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4028 node4028Labels := by rfl

def raw42975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42975Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42975step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42975step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42975step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42975step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42975step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42975 raw42975Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw42975 raw42975Labels = mixedMoment B raw42975step0 raw42975step0Labels := by
      have hz : ∀ j, raw42975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42975step0 = (fun i j => raw42975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42975step0 raw42975; decide +kernel
      have hl : raw42975step0Labels = raw42975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42975 raw42975Labels permutation434 hz
    mixedMoment B raw42975step0 raw42975step0Labels = mixedMoment B raw42975step1 raw42975step1Labels := by
      have ha : raw42975step1 = (fun i j => raw42975step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42975step1 raw42975step0; decide +kernel
      have hl : raw42975step1Labels = raw42975step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42975step0 raw42975step0Labels permutation150 permutation3
    mixedMoment B raw42975step1 raw42975step1Labels = mixedMoment B raw42975step2 raw42975step2Labels := by
      have ha : raw42975step2 = -raw42975step1 := by apply Matrix.ext; change ∀ i j, raw42975step2 i j = -(raw42975step1 i j); unfold raw42975step2 raw42975step1; decide +kernel
      have hl : raw42975step2Labels = raw42975step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42975step2 raw42975step2Labels = mixedMoment B raw42975step3 raw42975step3Labels := by
      have ha : raw42975step3 = raw42975step2 := by apply Matrix.ext; unfold raw42975step3 raw42975step2; decide +kernel
      have hl : raw42975step2Labels = labelEmbedding7 ∘ raw42975step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42975step2 raw42975step2Labels raw42975step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw42976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42976Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42976step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42976 raw42976Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw42976 raw42976Labels = mixedMoment B raw42976step0 raw42976step0Labels := by
      have ha : raw42976step0 = (fun i j => raw42976 (permutation409 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42976step0 raw42976; decide +kernel
      have hl : raw42976step0Labels = raw42976Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42976 raw42976Labels permutation409 permutation4
    mixedMoment B raw42976step0 raw42976step0Labels = mixedMoment B raw42976step1 raw42976step1Labels := by
      have ha : raw42976step1 = raw42976step0 := by apply Matrix.ext; unfold raw42976step1 raw42976step0; decide +kernel
      have hl : raw42976step0Labels = labelEmbedding1 ∘ raw42976step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42976step0 raw42976step0Labels raw42976step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw42977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42977Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42977 raw42977Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42977 raw42977Labels = mixedMoment B raw42977step0 raw42977step0Labels := by
      have ha : raw42977step0 = (fun i j => raw42977 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42977step0 raw42977; decide +kernel
      have hl : raw42977step0Labels = raw42977Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42977 raw42977Labels permutation399 permutation6
    mixedMoment B raw42977step0 raw42977step0Labels = mixedMoment B raw42977step1 raw42977step1Labels := by
      have ha : raw42977step1 = -raw42977step0 := by apply Matrix.ext; change ∀ i j, raw42977step1 i j = -(raw42977step0 i j); unfold raw42977step1 raw42977step0; decide +kernel
      have hl : raw42977step1Labels = raw42977step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw42978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42978Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw42978step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw42978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42978step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42978step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42978step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42978 raw42978Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw42978 raw42978Labels = mixedMoment B raw42978step0 raw42978step0Labels := by
      have hz : ∀ j, raw42978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42978step0 = (fun i j => raw42978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42978step0 raw42978; decide +kernel
      have hl : raw42978step0Labels = raw42978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42978 raw42978Labels permutation434 hz
    mixedMoment B raw42978step0 raw42978step0Labels = mixedMoment B raw42978step1 raw42978step1Labels := by
      have ha : raw42978step1 = (fun i j => raw42978step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42978step1 raw42978step0; decide +kernel
      have hl : raw42978step1Labels = raw42978step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42978step0 raw42978step0Labels permutation146 permutation2
    mixedMoment B raw42978step1 raw42978step1Labels = mixedMoment B raw42978step2 raw42978step2Labels := by
      have ha : raw42978step2 = -raw42978step1 := by apply Matrix.ext; change ∀ i j, raw42978step2 i j = -(raw42978step1 i j); unfold raw42978step2 raw42978step1; decide +kernel
      have hl : raw42978step2Labels = raw42978step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42978step2 raw42978step2Labels = mixedMoment B raw42978step3 raw42978step3Labels := by
      have ha : raw42978step3 = raw42978step2 := by apply Matrix.ext; unfold raw42978step3 raw42978step2; decide +kernel
      have hl : raw42978step2Labels = labelEmbedding1 ∘ raw42978step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42978step2 raw42978step2Labels raw42978step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw42979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42979Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw42979step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw42979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw42979step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42979 raw42979Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw42979 raw42979Labels = mixedMoment B raw42979step0 raw42979step0Labels := by
      have hz : ∀ j, raw42979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42979step0 = (fun i j => raw42979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42979step0 raw42979; decide +kernel
      have hl : raw42979step0Labels = raw42979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42979 raw42979Labels permutation434 hz
    mixedMoment B raw42979step0 raw42979step0Labels = mixedMoment B raw42979step1 raw42979step1Labels := by
      have ha : raw42979step1 = (fun i j => raw42979step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42979step1 raw42979step0; decide +kernel
      have hl : raw42979step1Labels = raw42979step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42979step0 raw42979step0Labels permutation92 permutation6
    mixedMoment B raw42979step1 raw42979step1Labels = mixedMoment B raw42979step2 raw42979step2Labels := by
      have ha : raw42979step2 = -raw42979step1 := by apply Matrix.ext; change ∀ i j, raw42979step2 i j = -(raw42979step1 i j); unfold raw42979step2 raw42979step1; decide +kernel
      have hl : raw42979step2Labels = raw42979step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw42980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42980Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw42980step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42980step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42980step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42980 raw42980Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw42980 raw42980Labels = mixedMoment B raw42980step0 raw42980step0Labels := by
      have hz : ∀ j, raw42980 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42980step0 = (fun i j => raw42980 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42980step0 raw42980; decide +kernel
      have hl : raw42980step0Labels = raw42980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42980 raw42980Labels permutation520 hz
    mixedMoment B raw42980step0 raw42980step0Labels = mixedMoment B raw42980step1 raw42980step1Labels := by
      have ha : raw42980step1 = (fun i j => raw42980step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42980step1 raw42980step0; decide +kernel
      have hl : raw42980step1Labels = raw42980step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42980step0 raw42980step0Labels permutation146 permutation2
    mixedMoment B raw42980step1 raw42980step1Labels = mixedMoment B raw42980step2 raw42980step2Labels := by
      have ha : raw42980step2 = -raw42980step1 := by apply Matrix.ext; change ∀ i j, raw42980step2 i j = -(raw42980step1 i j); unfold raw42980step2 raw42980step1; decide +kernel
      have hl : raw42980step2Labels = raw42980step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42980step2 raw42980step2Labels = mixedMoment B raw42980step3 raw42980step3Labels := by
      have ha : raw42980step3 = raw42980step2 := by apply Matrix.ext; unfold raw42980step3 raw42980step2; decide +kernel
      have hl : raw42980step2Labels = labelEmbedding1 ∘ raw42980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42980step2 raw42980step2Labels raw42980step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw42981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42981Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw42981step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42981step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42981step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42981 raw42981Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw42981 raw42981Labels = mixedMoment B raw42981step0 raw42981step0Labels := by
      have hz : ∀ j, raw42981 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42981step0 = (fun i j => raw42981 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42981step0 raw42981; decide +kernel
      have hl : raw42981step0Labels = raw42981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42981 raw42981Labels permutation520 hz
    mixedMoment B raw42981step0 raw42981step0Labels = mixedMoment B raw42981step1 raw42981step1Labels := by
      have ha : raw42981step1 = (fun i j => raw42981step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42981step1 raw42981step0; decide +kernel
      have hl : raw42981step1Labels = raw42981step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42981step0 raw42981step0Labels permutation136 permutation5
    mixedMoment B raw42981step1 raw42981step1Labels = mixedMoment B raw42981step2 raw42981step2Labels := by
      have ha : raw42981step2 = raw42981step1 := by apply Matrix.ext; unfold raw42981step2 raw42981step1; decide +kernel
      have hl : raw42981step1Labels = labelEmbedding9 ∘ raw42981step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42981step1 raw42981step1Labels raw42981step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw42982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42982Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42982 raw42982Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw42982 raw42982Labels = mixedMoment B raw42982step0 raw42982step0Labels := by
      have ha : raw42982step0 = (fun i j => raw42982 (permutation610 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42982step0 raw42982; decide +kernel
      have hl : raw42982step0Labels = raw42982Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42982 raw42982Labels permutation610 permutation4
    mixedMoment B raw42982step0 raw42982step0Labels = mixedMoment B raw42982step1 raw42982step1Labels := by
      have ha : raw42982step1 = raw42982step0 := by apply Matrix.ext; unfold raw42982step1 raw42982step0; decide +kernel
      have hl : raw42982step0Labels = labelEmbedding1 ∘ raw42982step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42982step0 raw42982step0Labels raw42982step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw42983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42983Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42983step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42983 raw42983Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42983 raw42983Labels = mixedMoment B raw42983step0 raw42983step0Labels := by
      have ha : raw42983step0 = (fun i j => raw42983 (permutation673 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42983step0 raw42983; decide +kernel
      have hl : raw42983step0Labels = raw42983Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42983 raw42983Labels permutation673 permutation5
    mixedMoment B raw42983step0 raw42983step0Labels = mixedMoment B raw42983step1 raw42983step1Labels := by
      have ha : raw42983step1 = raw42983step0 := by apply Matrix.ext; unfold raw42983step1 raw42983step0; decide +kernel
      have hl : raw42983step0Labels = labelEmbedding9 ∘ raw42983step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42983step0 raw42983step0Labels raw42983step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw42984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42984Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42984step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42984step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42984step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42984 raw42984Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw42984 raw42984Labels = mixedMoment B raw42984step0 raw42984step0Labels := by
      have ha : raw42984step0 = (fun i j => raw42984 (permutation434 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42984step0 raw42984; decide +kernel
      have hl : raw42984step0Labels = raw42984Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42984 raw42984Labels permutation434 permutation4
    mixedMoment B raw42984step0 raw42984step0Labels = mixedMoment B raw42984step1 raw42984step1Labels := by
      have ha : raw42984step1 = -raw42984step0 := by apply Matrix.ext; change ∀ i j, raw42984step1 i j = -(raw42984step0 i j); unfold raw42984step1 raw42984step0; decide +kernel
      have hl : raw42984step1Labels = raw42984step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42984step1 raw42984step1Labels = mixedMoment B raw42984step2 raw42984step2Labels := by
      have ha : raw42984step2 = raw42984step1 := by apply Matrix.ext; unfold raw42984step2 raw42984step1; decide +kernel
      have hl : raw42984step1Labels = labelEmbedding1 ∘ raw42984step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42984step1 raw42984step1Labels raw42984step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw42985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42985Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42985step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42985 raw42985Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw42985 raw42985Labels = mixedMoment B raw42985step0 raw42985step0Labels := by
      have ha : raw42985step0 = (fun i j => raw42985 (permutation673 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42985step0 raw42985; decide +kernel
      have hl : raw42985step0Labels = raw42985Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42985 raw42985Labels permutation673 permutation5
    mixedMoment B raw42985step0 raw42985step0Labels = mixedMoment B raw42985step1 raw42985step1Labels := by
      have ha : raw42985step1 = raw42985step0 := by apply Matrix.ext; unfold raw42985step1 raw42985step0; decide +kernel
      have hl : raw42985step0Labels = labelEmbedding9 ∘ raw42985step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42985step0 raw42985step0Labels raw42985step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw42986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42986Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42986step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42986 raw42986Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw42986 raw42986Labels = mixedMoment B raw42986step0 raw42986step0Labels := by
      have ha : raw42986step0 = (fun i j => raw42986 (permutation435 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42986step0 raw42986; decide +kernel
      have hl : raw42986step0Labels = raw42986Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42986 raw42986Labels permutation435 permutation4
    mixedMoment B raw42986step0 raw42986step0Labels = mixedMoment B raw42986step1 raw42986step1Labels := by
      have ha : raw42986step1 = -raw42986step0 := by apply Matrix.ext; change ∀ i j, raw42986step1 i j = -(raw42986step0 i j); unfold raw42986step1 raw42986step0; decide +kernel
      have hl : raw42986step1Labels = raw42986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42986step1 raw42986step1Labels = mixedMoment B raw42986step2 raw42986step2Labels := by
      have ha : raw42986step2 = raw42986step1 := by apply Matrix.ext; unfold raw42986step2 raw42986step1; decide +kernel
      have hl : raw42986step1Labels = labelEmbedding1 ∘ raw42986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42986step1 raw42986step1Labels raw42986step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw42987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42987Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42987step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42987step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42987step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42987step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42987 raw42987Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42987 raw42987Labels = mixedMoment B raw42987step0 raw42987step0Labels := by
      have ha : raw42987step0 = (fun i j => raw42987 (permutation435 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42987step0 raw42987; decide +kernel
      have hl : raw42987step0Labels = raw42987Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42987 raw42987Labels permutation435 permutation4
    mixedMoment B raw42987step0 raw42987step0Labels = mixedMoment B raw42987step1 raw42987step1Labels := by
      have ha : raw42987step1 = -raw42987step0 := by apply Matrix.ext; change ∀ i j, raw42987step1 i j = -(raw42987step0 i j); unfold raw42987step1 raw42987step0; decide +kernel
      have hl : raw42987step1Labels = raw42987step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42987step1 raw42987step1Labels = mixedMoment B raw42987step2 raw42987step2Labels := by
      have ha : raw42987step2 = raw42987step1 := by apply Matrix.ext; unfold raw42987step2 raw42987step1; decide +kernel
      have hl : raw42987step1Labels = labelEmbedding10 ∘ raw42987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42987step1 raw42987step1Labels raw42987step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw42988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42988Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42988step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42988 raw42988Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw42988 raw42988Labels = mixedMoment B raw42988step0 raw42988step0Labels := by
      have ha : raw42988step0 = (fun i j => raw42988 (permutation534 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42988step0 raw42988; decide +kernel
      have hl : raw42988step0Labels = raw42988Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42988 raw42988Labels permutation534 permutation4
    mixedMoment B raw42988step0 raw42988step0Labels = mixedMoment B raw42988step1 raw42988step1Labels := by
      have ha : raw42988step1 = raw42988step0 := by apply Matrix.ext; unfold raw42988step1 raw42988step0; decide +kernel
      have hl : raw42988step0Labels = labelEmbedding1 ∘ raw42988step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42988step0 raw42988step0Labels raw42988step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw42989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42989Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42989step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42989 raw42989Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw42989 raw42989Labels = mixedMoment B raw42989step0 raw42989step0Labels := by
      have ha : raw42989step0 = (fun i j => raw42989 (permutation534 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42989step0 raw42989; decide +kernel
      have hl : raw42989step0Labels = raw42989Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42989 raw42989Labels permutation534 permutation4
    mixedMoment B raw42989step0 raw42989step0Labels = mixedMoment B raw42989step1 raw42989step1Labels := by
      have ha : raw42989step1 = raw42989step0 := by apply Matrix.ext; unfold raw42989step1 raw42989step0; decide +kernel
      have hl : raw42989step0Labels = labelEmbedding10 ∘ raw42989step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42989step0 raw42989step0Labels raw42989step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw42990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42990Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42990step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42990step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42990 raw42990Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw42990 raw42990Labels = mixedMoment B raw42990step0 raw42990step0Labels := by
      have ha : raw42990step0 = (fun i j => raw42990 (permutation659 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42990step0 raw42990; decide +kernel
      have hl : raw42990step0Labels = raw42990Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42990 raw42990Labels permutation659 permutation2
    mixedMoment B raw42990step0 raw42990step0Labels = mixedMoment B raw42990step1 raw42990step1Labels := by
      have ha : raw42990step1 = -raw42990step0 := by apply Matrix.ext; change ∀ i j, raw42990step1 i j = -(raw42990step0 i j); unfold raw42990step1 raw42990step0; decide +kernel
      have hl : raw42990step1Labels = raw42990step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42990step1 raw42990step1Labels = mixedMoment B raw42990step2 raw42990step2Labels := by
      have ha : raw42990step2 = raw42990step1 := by apply Matrix.ext; unfold raw42990step2 raw42990step1; decide +kernel
      have hl : raw42990step1Labels = labelEmbedding1 ∘ raw42990step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42990step1 raw42990step1Labels raw42990step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3226 node3226Labels := by rfl

def raw42991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42991Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42991step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42991step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42991step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42991 raw42991Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw42991 raw42991Labels = mixedMoment B raw42991step0 raw42991step0Labels := by
      have ha : raw42991step0 = (fun i j => raw42991 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42991step0 raw42991; decide +kernel
      have hl : raw42991step0Labels = raw42991Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42991 raw42991Labels permutation662 permutation3
    mixedMoment B raw42991step0 raw42991step0Labels = mixedMoment B raw42991step1 raw42991step1Labels := by
      have ha : raw42991step1 = -raw42991step0 := by apply Matrix.ext; change ∀ i j, raw42991step1 i j = -(raw42991step0 i j); unfold raw42991step1 raw42991step0; decide +kernel
      have hl : raw42991step1Labels = raw42991step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42991step1 raw42991step1Labels = mixedMoment B raw42991step2 raw42991step2Labels := by
      have ha : raw42991step2 = raw42991step1 := by apply Matrix.ext; unfold raw42991step2 raw42991step1; decide +kernel
      have hl : raw42991step1Labels = labelEmbedding7 ∘ raw42991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42991step1 raw42991step1Labels raw42991step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw42992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42992Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42992 raw42992Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw42992 raw42992Labels = mixedMoment B raw42992step0 raw42992step0Labels := by
      have ha : raw42992step0 = (fun i j => raw42992 (permutation607 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42992step0 raw42992; decide +kernel
      have hl : raw42992step0Labels = raw42992Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42992 raw42992Labels permutation607 permutation4
    mixedMoment B raw42992step0 raw42992step0Labels = mixedMoment B raw42992step1 raw42992step1Labels := by
      have ha : raw42992step1 = raw42992step0 := by apply Matrix.ext; unfold raw42992step1 raw42992step0; decide +kernel
      have hl : raw42992step0Labels = labelEmbedding1 ∘ raw42992step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42992step0 raw42992step0Labels raw42992step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw42993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42993Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42993step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42993 raw42993Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw42993 raw42993Labels = mixedMoment B raw42993step0 raw42993step0Labels := by
      have ha : raw42993step0 = (fun i j => raw42993 (permutation611 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42993step0 raw42993; decide +kernel
      have hl : raw42993step0Labels = raw42993Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42993 raw42993Labels permutation611 permutation5
    mixedMoment B raw42993step0 raw42993step0Labels = mixedMoment B raw42993step1 raw42993step1Labels := by
      have ha : raw42993step1 = raw42993step0 := by apply Matrix.ext; unfold raw42993step1 raw42993step0; decide +kernel
      have hl : raw42993step0Labels = labelEmbedding9 ∘ raw42993step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42993step0 raw42993step0Labels raw42993step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw42994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42994Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 2, -3], ![2, -3, 1]]
def raw42994step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42994 raw42994Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw42994 raw42994Labels = mixedMoment B raw42994step0 raw42994step0Labels := by
      have hz : ∀ j, raw42994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42994step0 = (fun i j => raw42994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42994step0 raw42994; decide +kernel
      have hl : raw42994step0Labels = raw42994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42994 raw42994Labels permutation434 hz
    mixedMoment B raw42994step0 raw42994step0Labels = mixedMoment B raw42994step1 raw42994step1Labels := by
      have ha : raw42994step1 = (fun i j => raw42994step0 (permutation136 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42994step1 raw42994step0; decide +kernel
      have hl : raw42994step1Labels = raw42994step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42994step0 raw42994step0Labels permutation136 permutation4
    mixedMoment B raw42994step1 raw42994step1Labels = mixedMoment B raw42994step2 raw42994step2Labels := by
      have ha : raw42994step2 = raw42994step1 := by apply Matrix.ext; unfold raw42994step2 raw42994step1; decide +kernel
      have hl : raw42994step1Labels = labelEmbedding1 ∘ raw42994step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42994step1 raw42994step1Labels raw42994step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw42995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42995Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 2, -3], ![2, -3, 1]]
def raw42995step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42995step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42995 raw42995Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw42995 raw42995Labels = mixedMoment B raw42995step0 raw42995step0Labels := by
      have hz : ∀ j, raw42995 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42995step0 = (fun i j => raw42995 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42995step0 raw42995; decide +kernel
      have hl : raw42995step0Labels = raw42995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42995 raw42995Labels permutation434 hz
    mixedMoment B raw42995step0 raw42995step0Labels = mixedMoment B raw42995step1 raw42995step1Labels := by
      have ha : raw42995step1 = (fun i j => raw42995step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42995step1 raw42995step0; decide +kernel
      have hl : raw42995step1Labels = raw42995step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42995step0 raw42995step0Labels permutation104 permutation6
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw42996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42996Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 2, -4]]
def raw42996step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42996 raw42996Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw42996 raw42996Labels = mixedMoment B raw42996step0 raw42996step0Labels := by
      have hz : ∀ j, raw42996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42996step0 = (fun i j => raw42996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42996step0 raw42996; decide +kernel
      have hl : raw42996step0Labels = raw42996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42996 raw42996Labels permutation434 hz
    mixedMoment B raw42996step0 raw42996step0Labels = mixedMoment B raw42996step1 raw42996step1Labels := by
      have ha : raw42996step1 = (fun i j => raw42996step0 (permutation112 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42996step1 raw42996step0; decide +kernel
      have hl : raw42996step1Labels = raw42996step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42996step0 raw42996step0Labels permutation112 permutation4
    mixedMoment B raw42996step1 raw42996step1Labels = mixedMoment B raw42996step2 raw42996step2Labels := by
      have ha : raw42996step2 = raw42996step1 := by apply Matrix.ext; unfold raw42996step2 raw42996step1; decide +kernel
      have hl : raw42996step1Labels = labelEmbedding1 ∘ raw42996step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42996step1 raw42996step1Labels raw42996step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw42997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42997Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 2, -4]]
def raw42997step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42997 raw42997Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw42997 raw42997Labels = mixedMoment B raw42997step0 raw42997step0Labels := by
      have hz : ∀ j, raw42997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42997step0 = (fun i j => raw42997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42997step0 raw42997; decide +kernel
      have hl : raw42997step0Labels = raw42997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42997 raw42997Labels permutation434 hz
    mixedMoment B raw42997step0 raw42997step0Labels = mixedMoment B raw42997step1 raw42997step1Labels := by
      have ha : raw42997step1 = (fun i j => raw42997step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42997step1 raw42997step0; decide +kernel
      have hl : raw42997step1Labels = raw42997step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42997step0 raw42997step0Labels permutation128 permutation6
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw42998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42998Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42998step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42998step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42998 raw42998Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw42998 raw42998Labels = mixedMoment B raw42998step0 raw42998step0Labels := by
      have ha : raw42998step0 = (fun i j => raw42998 (permutation520 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42998step0 raw42998; decide +kernel
      have hl : raw42998step0Labels = raw42998Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42998 raw42998Labels permutation520 permutation4
    mixedMoment B raw42998step0 raw42998step0Labels = mixedMoment B raw42998step1 raw42998step1Labels := by
      have ha : raw42998step1 = -raw42998step0 := by apply Matrix.ext; change ∀ i j, raw42998step1 i j = -(raw42998step0 i j); unfold raw42998step1 raw42998step0; decide +kernel
      have hl : raw42998step1Labels = raw42998step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42998step1 raw42998step1Labels = mixedMoment B raw42998step2 raw42998step2Labels := by
      have ha : raw42998step2 = raw42998step1 := by apply Matrix.ext; unfold raw42998step2 raw42998step1; decide +kernel
      have hl : raw42998step1Labels = labelEmbedding1 ∘ raw42998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42998step1 raw42998step1Labels raw42998step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw42999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42999Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42999 raw42999Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw42999 raw42999Labels = mixedMoment B raw42999step0 raw42999step0Labels := by
      have ha : raw42999step0 = (fun i j => raw42999 (permutation526 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42999step0 raw42999; decide +kernel
      have hl : raw42999step0Labels = raw42999Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42999 raw42999Labels permutation526 permutation6
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw43000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw43000Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw43000step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw43000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43000step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw43000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43000 raw43000Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw43000 raw43000Labels = mixedMoment B raw43000step0 raw43000step0Labels := by
      have ha : raw43000step0 = (fun i j => raw43000 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43000step0 raw43000; decide +kernel
      have hl : raw43000step0Labels = raw43000Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43000 raw43000Labels permutation590 permutation4
    mixedMoment B raw43000step0 raw43000step0Labels = mixedMoment B raw43000step1 raw43000step1Labels := by
      have ha : raw43000step1 = -raw43000step0 := by apply Matrix.ext; change ∀ i j, raw43000step1 i j = -(raw43000step0 i j); unfold raw43000step1 raw43000step0; decide +kernel
      have hl : raw43000step1Labels = raw43000step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43000step1 raw43000step1Labels = mixedMoment B raw43000step2 raw43000step2Labels := by
      have ha : raw43000step2 = raw43000step1 := by apply Matrix.ext; unfold raw43000step2 raw43000step1; decide +kernel
      have hl : raw43000step1Labels = labelEmbedding1 ∘ raw43000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43000step1 raw43000step1Labels raw43000step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw43001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw43001Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43001 raw43001Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw43001 raw43001Labels = mixedMoment B raw43001step0 raw43001step0Labels := by
      have ha : raw43001step0 = (fun i j => raw43001 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43001step0 raw43001; decide +kernel
      have hl : raw43001step0Labels = raw43001Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43001 raw43001Labels permutation590 permutation6
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw43002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw43002Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw43002step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw43002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43002step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw43002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43002 raw43002Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw43002 raw43002Labels = mixedMoment B raw43002step0 raw43002step0Labels := by
      have ha : raw43002step0 = (fun i j => raw43002 (permutation591 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43002step0 raw43002; decide +kernel
      have hl : raw43002step0Labels = raw43002Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43002 raw43002Labels permutation591 permutation4
    mixedMoment B raw43002step0 raw43002step0Labels = mixedMoment B raw43002step1 raw43002step1Labels := by
      have ha : raw43002step1 = -raw43002step0 := by apply Matrix.ext; change ∀ i j, raw43002step1 i j = -(raw43002step0 i j); unfold raw43002step1 raw43002step0; decide +kernel
      have hl : raw43002step1Labels = raw43002step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43002step1 raw43002step1Labels = mixedMoment B raw43002step2 raw43002step2Labels := by
      have ha : raw43002step2 = raw43002step1 := by apply Matrix.ext; unfold raw43002step2 raw43002step1; decide +kernel
      have hl : raw43002step1Labels = labelEmbedding1 ∘ raw43002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43002step1 raw43002step1Labels raw43002step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw43003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw43003Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw43003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43003 raw43003Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw43003 raw43003Labels = mixedMoment B raw43003step0 raw43003step0Labels := by
      have ha : raw43003step0 = (fun i j => raw43003 (permutation599 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43003step0 raw43003; decide +kernel
      have hl : raw43003step0Labels = raw43003Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43003 raw43003Labels permutation599 permutation6
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw43004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw43004Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw43004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43004step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43004 raw43004Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw43004 raw43004Labels = mixedMoment B raw43004step0 raw43004step0Labels := by
      have ha : raw43004step0 = (fun i j => raw43004 (permutation443 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43004step0 raw43004; decide +kernel
      have hl : raw43004step0Labels = raw43004Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43004 raw43004Labels permutation443 permutation4
    mixedMoment B raw43004step0 raw43004step0Labels = mixedMoment B raw43004step1 raw43004step1Labels := by
      have ha : raw43004step1 = -raw43004step0 := by apply Matrix.ext; change ∀ i j, raw43004step1 i j = -(raw43004step0 i j); unfold raw43004step1 raw43004step0; decide +kernel
      have hl : raw43004step1Labels = raw43004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43004step1 raw43004step1Labels = mixedMoment B raw43004step2 raw43004step2Labels := by
      have ha : raw43004step2 = raw43004step1 := by apply Matrix.ext; unfold raw43004step2 raw43004step1; decide +kernel
      have hl : raw43004step1Labels = labelEmbedding1 ∘ raw43004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43004step1 raw43004step1Labels raw43004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw43005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw43005Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw43005step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43005step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43005step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43005step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43005 raw43005Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw43005 raw43005Labels = mixedMoment B raw43005step0 raw43005step0Labels := by
      have ha : raw43005step0 = (fun i j => raw43005 (permutation443 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43005step0 raw43005; decide +kernel
      have hl : raw43005step0Labels = raw43005Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43005 raw43005Labels permutation443 permutation4
    mixedMoment B raw43005step0 raw43005step0Labels = mixedMoment B raw43005step1 raw43005step1Labels := by
      have ha : raw43005step1 = -raw43005step0 := by apply Matrix.ext; change ∀ i j, raw43005step1 i j = -(raw43005step0 i j); unfold raw43005step1 raw43005step0; decide +kernel
      have hl : raw43005step1Labels = raw43005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43005step1 raw43005step1Labels = mixedMoment B raw43005step2 raw43005step2Labels := by
      have ha : raw43005step2 = raw43005step1 := by apply Matrix.ext; unfold raw43005step2 raw43005step1; decide +kernel
      have hl : raw43005step1Labels = labelEmbedding10 ∘ raw43005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43005step1 raw43005step1Labels raw43005step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw43006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw43006Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw43006step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw43006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43006step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw43006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43006 raw43006Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw43006 raw43006Labels = mixedMoment B raw43006step0 raw43006step0Labels := by
      have ha : raw43006step0 = (fun i j => raw43006 (permutation439 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43006step0 raw43006; decide +kernel
      have hl : raw43006step0Labels = raw43006Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43006 raw43006Labels permutation439 permutation4
    mixedMoment B raw43006step0 raw43006step0Labels = mixedMoment B raw43006step1 raw43006step1Labels := by
      have ha : raw43006step1 = -raw43006step0 := by apply Matrix.ext; change ∀ i j, raw43006step1 i j = -(raw43006step0 i j); unfold raw43006step1 raw43006step0; decide +kernel
      have hl : raw43006step1Labels = raw43006step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43006step1 raw43006step1Labels = mixedMoment B raw43006step2 raw43006step2Labels := by
      have ha : raw43006step2 = raw43006step1 := by apply Matrix.ext; unfold raw43006step2 raw43006step1; decide +kernel
      have hl : raw43006step1Labels = labelEmbedding1 ∘ raw43006step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43006step1 raw43006step1Labels raw43006step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw43007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw43007Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw43007step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw43007step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43007step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw43007step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43007 raw43007Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw43007 raw43007Labels = mixedMoment B raw43007step0 raw43007step0Labels := by
      have ha : raw43007step0 = (fun i j => raw43007 (permutation439 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43007step0 raw43007; decide +kernel
      have hl : raw43007step0Labels = raw43007Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43007 raw43007Labels permutation439 permutation4
    mixedMoment B raw43007step0 raw43007step0Labels = mixedMoment B raw43007step1 raw43007step1Labels := by
      have ha : raw43007step1 = -raw43007step0 := by apply Matrix.ext; change ∀ i j, raw43007step1 i j = -(raw43007step0 i j); unfold raw43007step1 raw43007step0; decide +kernel
      have hl : raw43007step1Labels = raw43007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43007step1 raw43007step1Labels = mixedMoment B raw43007step2 raw43007step2Labels := by
      have ha : raw43007step2 = raw43007step1 := by apply Matrix.ext; unfold raw43007step2 raw43007step1; decide +kernel
      have hl : raw43007step1Labels = labelEmbedding10 ∘ raw43007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43007step1 raw43007step1Labels raw43007step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
