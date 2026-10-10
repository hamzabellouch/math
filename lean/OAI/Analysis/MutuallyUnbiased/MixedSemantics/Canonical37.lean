import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4736step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4736step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4736step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4736 raw4736Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw4736 raw4736Labels = mixedMoment B raw4736step0 raw4736step0Labels := by
      have hz : ∀ j, raw4736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4736step0 = (fun i j => raw4736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4736step0 raw4736; decide +kernel
      have hl : raw4736step0Labels = raw4736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4736 raw4736Labels permutation346 hz
    mixedMoment B raw4736step0 raw4736step0Labels = mixedMoment B raw4736step1 raw4736step1Labels := by
      have hz : ∀ j, raw4736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4736step1 = (fun i j => raw4736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4736step1 raw4736step0; decide +kernel
      have hl : raw4736step1Labels = raw4736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4736step0 raw4736step0Labels permutation56 hz
    mixedMoment B raw4736step1 raw4736step1Labels = mixedMoment B raw4736step2 raw4736step2Labels := by
      have ha : raw4736step2 = (fun i j => raw4736step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4736step2 raw4736step1; decide +kernel
      have hl : raw4736step2Labels = raw4736step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4736step1 raw4736step1Labels permutation31 permutation7
    mixedMoment B raw4736step2 raw4736step2Labels = mixedMoment B raw4736step3 raw4736step3Labels := by
      have ha : raw4736step3 = raw4736step2 := by apply Matrix.ext; unfold raw4736step3 raw4736step2; decide +kernel
      have hl : raw4736step2Labels = labelEmbedding1 ∘ raw4736step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4736step2 raw4736step2Labels raw4736step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw4737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4737step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4737step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4737 raw4737Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw4737 raw4737Labels = mixedMoment B raw4737step0 raw4737step0Labels := by
      have hz : ∀ j, raw4737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4737step0 = (fun i j => raw4737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4737step0 raw4737; decide +kernel
      have hl : raw4737step0Labels = raw4737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4737 raw4737Labels permutation346 hz
    mixedMoment B raw4737step0 raw4737step0Labels = mixedMoment B raw4737step1 raw4737step1Labels := by
      have hz : ∀ j, raw4737step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4737step1 = (fun i j => raw4737step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4737step1 raw4737step0; decide +kernel
      have hl : raw4737step1Labels = raw4737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4737step0 raw4737step0Labels permutation56 hz
    mixedMoment B raw4737step1 raw4737step1Labels = mixedMoment B raw4737step2 raw4737step2Labels := by
      have ha : raw4737step2 = (fun i j => raw4737step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4737step2 raw4737step1; decide +kernel
      have hl : raw4737step2Labels = raw4737step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4737step1 raw4737step1Labels permutation29 permutation7
    mixedMoment B raw4737step2 raw4737step2Labels = mixedMoment B raw4737step3 raw4737step3Labels := by
      have ha : raw4737step3 = raw4737step2 := by apply Matrix.ext; unfold raw4737step3 raw4737step2; decide +kernel
      have hl : raw4737step2Labels = labelEmbedding1 ∘ raw4737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4737step2 raw4737step2Labels raw4737step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw4738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4738 raw4738Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw4738 raw4738Labels = mixedMoment B raw4738step0 raw4738step0Labels := by
      have hz : ∀ j, raw4738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4738step0 = (fun i j => raw4738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4738step0 raw4738; decide +kernel
      have hl : raw4738step0Labels = raw4738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4738 raw4738Labels permutation346 hz
    mixedMoment B raw4738step0 raw4738step0Labels = mixedMoment B raw4738step1 raw4738step1Labels := by
      have hz : ∀ j, raw4738step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4738step1 = (fun i j => raw4738step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4738step1 raw4738step0; decide +kernel
      have hl : raw4738step1Labels = raw4738step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4738step0 raw4738step0Labels permutation56 hz
    mixedMoment B raw4738step1 raw4738step1Labels = mixedMoment B raw4738step2 raw4738step2Labels := by
      have ha : raw4738step2 = (fun i j => raw4738step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4738step2 raw4738step1; decide +kernel
      have hl : raw4738step2Labels = raw4738step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4738step1 raw4738step1Labels permutation29 permutation2
    mixedMoment B raw4738step2 raw4738step2Labels = mixedMoment B raw4738step3 raw4738step3Labels := by
      have ha : raw4738step3 = -raw4738step2 := by apply Matrix.ext; change ∀ i j, raw4738step3 i j = -(raw4738step2 i j); unfold raw4738step3 raw4738step2; decide +kernel
      have hl : raw4738step3Labels = raw4738step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw4739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4739 raw4739Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw4739 raw4739Labels = mixedMoment B raw4739step0 raw4739step0Labels := by
      have hz : ∀ j, raw4739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4739step0 = (fun i j => raw4739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4739step0 raw4739; decide +kernel
      have hl : raw4739step0Labels = raw4739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4739 raw4739Labels permutation346 hz
    mixedMoment B raw4739step0 raw4739step0Labels = mixedMoment B raw4739step1 raw4739step1Labels := by
      have ha : raw4739step1 = (fun i j => raw4739step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4739step1 raw4739step0; decide +kernel
      have hl : raw4739step1Labels = raw4739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4739step0 raw4739step0Labels permutation145 permutation2
    mixedMoment B raw4739step1 raw4739step1Labels = mixedMoment B raw4739step2 raw4739step2Labels := by
      have ha : raw4739step2 = -raw4739step1 := by apply Matrix.ext; change ∀ i j, raw4739step2 i j = -(raw4739step1 i j); unfold raw4739step2 raw4739step1; decide +kernel
      have hl : raw4739step2Labels = raw4739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw4740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4740 raw4740Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw4740 raw4740Labels = mixedMoment B raw4740step0 raw4740step0Labels := by
      have hz : ∀ j, raw4740 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4740step0 = (fun i j => raw4740 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4740step0 raw4740; decide +kernel
      have hl : raw4740step0Labels = raw4740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4740 raw4740Labels permutation265 hz
    mixedMoment B raw4740step0 raw4740step0Labels = mixedMoment B raw4740step1 raw4740step1Labels := by
      have ha : raw4740step1 = (fun i j => raw4740step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4740step1 raw4740step0; decide +kernel
      have hl : raw4740step1Labels = raw4740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4740step0 raw4740step0Labels permutation145 permutation2
    mixedMoment B raw4740step1 raw4740step1Labels = mixedMoment B raw4740step2 raw4740step2Labels := by
      have ha : raw4740step2 = -raw4740step1 := by apply Matrix.ext; change ∀ i j, raw4740step2 i j = -(raw4740step1 i j); unfold raw4740step2 raw4740step1; decide +kernel
      have hl : raw4740step2Labels = raw4740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw4741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4741 raw4741Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw4741 raw4741Labels = mixedMoment B raw4741step0 raw4741step0Labels := by
      have hz : ∀ j, raw4741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4741step0 = (fun i j => raw4741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4741step0 raw4741; decide +kernel
      have hl : raw4741step0Labels = raw4741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4741 raw4741Labels permutation346 hz
    mixedMoment B raw4741step0 raw4741step0Labels = mixedMoment B raw4741step1 raw4741step1Labels := by
      have hz : ∀ j, raw4741step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4741step1 = (fun i j => raw4741step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4741step1 raw4741step0; decide +kernel
      have hl : raw4741step1Labels = raw4741step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4741step0 raw4741step0Labels permutation56 hz
    mixedMoment B raw4741step1 raw4741step1Labels = mixedMoment B raw4741step2 raw4741step2Labels := by
      have ha : raw4741step2 = (fun i j => raw4741step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4741step2 raw4741step1; decide +kernel
      have hl : raw4741step2Labels = raw4741step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4741step1 raw4741step1Labels permutation31 permutation2
    mixedMoment B raw4741step2 raw4741step2Labels = mixedMoment B raw4741step3 raw4741step3Labels := by
      have ha : raw4741step3 = -raw4741step2 := by apply Matrix.ext; change ∀ i j, raw4741step3 i j = -(raw4741step2 i j); unfold raw4741step3 raw4741step2; decide +kernel
      have hl : raw4741step3Labels = raw4741step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw4742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4742 raw4742Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw4742 raw4742Labels = mixedMoment B raw4742step0 raw4742step0Labels := by
      have hz : ∀ j, raw4742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4742step0 = (fun i j => raw4742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4742step0 raw4742; decide +kernel
      have hl : raw4742step0Labels = raw4742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4742 raw4742Labels permutation346 hz
    mixedMoment B raw4742step0 raw4742step0Labels = mixedMoment B raw4742step1 raw4742step1Labels := by
      have hz : ∀ j, raw4742step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4742step1 = (fun i j => raw4742step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4742step1 raw4742step0; decide +kernel
      have hl : raw4742step1Labels = raw4742step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4742step0 raw4742step0Labels permutation56 hz
    mixedMoment B raw4742step1 raw4742step1Labels = mixedMoment B raw4742step2 raw4742step2Labels := by
      have ha : raw4742step2 = (fun i j => raw4742step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4742step2 raw4742step1; decide +kernel
      have hl : raw4742step2Labels = raw4742step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4742step1 raw4742step1Labels permutation29 permutation2
    mixedMoment B raw4742step2 raw4742step2Labels = mixedMoment B raw4742step3 raw4742step3Labels := by
      have ha : raw4742step3 = -raw4742step2 := by apply Matrix.ext; change ∀ i j, raw4742step3 i j = -(raw4742step2 i j); unfold raw4742step3 raw4742step2; decide +kernel
      have hl : raw4742step3Labels = raw4742step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw4743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw4743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4743 raw4743Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw4743 raw4743Labels = mixedMoment B raw4743step0 raw4743step0Labels := by
      have hz : ∀ j, raw4743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4743step0 = (fun i j => raw4743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4743step0 raw4743; decide +kernel
      have hl : raw4743step0Labels = raw4743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4743 raw4743Labels permutation346 hz
    mixedMoment B raw4743step0 raw4743step0Labels = mixedMoment B raw4743step1 raw4743step1Labels := by
      have hz : ∀ j, raw4743step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4743step1 = (fun i j => raw4743step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4743step1 raw4743step0; decide +kernel
      have hl : raw4743step1Labels = raw4743step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4743step0 raw4743step0Labels permutation56 hz
    mixedMoment B raw4743step1 raw4743step1Labels = mixedMoment B raw4743step2 raw4743step2Labels := by
      have ha : raw4743step2 = (fun i j => raw4743step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4743step2 raw4743step1; decide +kernel
      have hl : raw4743step2Labels = raw4743step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4743step1 raw4743step1Labels permutation29 permutation2
    mixedMoment B raw4743step2 raw4743step2Labels = mixedMoment B raw4743step3 raw4743step3Labels := by
      have ha : raw4743step3 = -raw4743step2 := by apply Matrix.ext; change ∀ i j, raw4743step3 i j = -(raw4743step2 i j); unfold raw4743step3 raw4743step2; decide +kernel
      have hl : raw4743step3Labels = raw4743step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3623 node3623Labels := by rfl

def raw4744 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3]]
def raw4744Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4744step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3]]
def raw4744step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4744step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw4744step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4744step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw4744step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4744step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw4744step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical4744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4744 raw4744Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw4744 raw4744Labels = mixedMoment B raw4744step0 raw4744step0Labels := by
      have hz : ∀ j, raw4744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4744step0 = (fun i j => raw4744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4744step0 raw4744; decide +kernel
      have hl : raw4744step0Labels = raw4744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4744 raw4744Labels permutation346 hz
    mixedMoment B raw4744step0 raw4744step0Labels = mixedMoment B raw4744step1 raw4744step1Labels := by
      have hz : ∀ j, raw4744step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4744step1 = (fun i j => raw4744step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4744step1 raw4744step0; decide +kernel
      have hl : raw4744step1Labels = raw4744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4744step0 raw4744step0Labels permutation56 hz
    mixedMoment B raw4744step1 raw4744step1Labels = mixedMoment B raw4744step2 raw4744step2Labels := by
      have ha : raw4744step2 = (fun i j => raw4744step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4744step2 raw4744step1; decide +kernel
      have hl : raw4744step2Labels = raw4744step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4744step1 raw4744step1Labels permutation26 permutation0
    mixedMoment B raw4744step2 raw4744step2Labels = mixedMoment B raw4744step3 raw4744step3Labels := by
      have ha : raw4744step3 = -raw4744step2 := by apply Matrix.ext; change ∀ i j, raw4744step3 i j = -(raw4744step2 i j); unfold raw4744step3 raw4744step2; decide +kernel
      have hl : raw4744step3Labels = raw4744step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw4745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4745 raw4745Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw4745 raw4745Labels = mixedMoment B raw4745step0 raw4745step0Labels := by
      have hz : ∀ j, raw4745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4745step0 = (fun i j => raw4745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4745step0 raw4745; decide +kernel
      have hl : raw4745step0Labels = raw4745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4745 raw4745Labels permutation346 hz
    mixedMoment B raw4745step0 raw4745step0Labels = mixedMoment B raw4745step1 raw4745step1Labels := by
      have ha : raw4745step1 = (fun i j => raw4745step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4745step1 raw4745step0; decide +kernel
      have hl : raw4745step1Labels = raw4745step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4745step0 raw4745step0Labels permutation40 permutation2
    _ = mixedMoment B node1385 node1385Labels := by rfl

def raw4746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4746 raw4746Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw4746 raw4746Labels = mixedMoment B raw4746step0 raw4746step0Labels := by
      have hz : ∀ j, raw4746 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4746step0 = (fun i j => raw4746 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4746step0 raw4746; decide +kernel
      have hl : raw4746step0Labels = raw4746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4746 raw4746Labels permutation265 hz
    mixedMoment B raw4746step0 raw4746step0Labels = mixedMoment B raw4746step1 raw4746step1Labels := by
      have ha : raw4746step1 = (fun i j => raw4746step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4746step1 raw4746step0; decide +kernel
      have hl : raw4746step1Labels = raw4746step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4746step0 raw4746step0Labels permutation40 permutation2
    _ = mixedMoment B node1385 node1385Labels := by rfl

def raw4747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4747step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4747 raw4747Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw4747 raw4747Labels = mixedMoment B raw4747step0 raw4747step0Labels := by
      have hz : ∀ j, raw4747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4747step0 = (fun i j => raw4747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4747step0 raw4747; decide +kernel
      have hl : raw4747step0Labels = raw4747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4747 raw4747Labels permutation346 hz
    mixedMoment B raw4747step0 raw4747step0Labels = mixedMoment B raw4747step1 raw4747step1Labels := by
      have hz : ∀ j, raw4747step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4747step1 = (fun i j => raw4747step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4747step1 raw4747step0; decide +kernel
      have hl : raw4747step1Labels = raw4747step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4747step0 raw4747step0Labels permutation56 hz
    mixedMoment B raw4747step1 raw4747step1Labels = mixedMoment B raw4747step2 raw4747step2Labels := by
      have ha : raw4747step2 = (fun i j => raw4747step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4747step2 raw4747step1; decide +kernel
      have hl : raw4747step2Labels = raw4747step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4747step1 raw4747step1Labels permutation10 permutation2
    _ = mixedMoment B node1408 node1408Labels := by rfl

def raw4748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4748 raw4748Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw4748 raw4748Labels = mixedMoment B raw4748step0 raw4748step0Labels := by
      have hz : ∀ j, raw4748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4748step0 = (fun i j => raw4748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4748step0 raw4748; decide +kernel
      have hl : raw4748step0Labels = raw4748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4748 raw4748Labels permutation346 hz
    mixedMoment B raw4748step0 raw4748step0Labels = mixedMoment B raw4748step1 raw4748step1Labels := by
      have hz : ∀ j, raw4748step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4748step1 = (fun i j => raw4748step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4748step1 raw4748step0; decide +kernel
      have hl : raw4748step1Labels = raw4748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4748step0 raw4748step0Labels permutation56 hz
    _ = mixedMoment B node1408 node1408Labels := by rfl

def raw4749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw4749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4749step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4749 raw4749Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw4749 raw4749Labels = mixedMoment B raw4749step0 raw4749step0Labels := by
      have hz : ∀ j, raw4749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4749step0 = (fun i j => raw4749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4749step0 raw4749; decide +kernel
      have hl : raw4749step0Labels = raw4749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4749 raw4749Labels permutation346 hz
    mixedMoment B raw4749step0 raw4749step0Labels = mixedMoment B raw4749step1 raw4749step1Labels := by
      have hz : ∀ j, raw4749step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4749step1 = (fun i j => raw4749step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4749step1 raw4749step0; decide +kernel
      have hl : raw4749step1Labels = raw4749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4749step0 raw4749step0Labels permutation56 hz
    mixedMoment B raw4749step1 raw4749step1Labels = mixedMoment B raw4749step2 raw4749step2Labels := by
      have ha : raw4749step2 = (fun i j => raw4749step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4749step2 raw4749step1; decide +kernel
      have hl : raw4749step2Labels = raw4749step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4749step1 raw4749step1Labels permutation29 permutation2
    mixedMoment B raw4749step2 raw4749step2Labels = mixedMoment B raw4749step3 raw4749step3Labels := by
      have ha : raw4749step3 = -raw4749step2 := by apply Matrix.ext; change ∀ i j, raw4749step3 i j = -(raw4749step2 i j); unfold raw4749step3 raw4749step2; decide +kernel
      have hl : raw4749step3Labels = raw4749step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1027 node1027Labels := by rfl

def raw4750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4750 raw4750Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw4750 raw4750Labels = mixedMoment B raw4750step0 raw4750step0Labels := by
      have ha : raw4750step0 = (fun i j => raw4750 (permutation616 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4750step0 raw4750; decide +kernel
      have hl : raw4750step0Labels = raw4750Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4750 raw4750Labels permutation616 permutation2
    mixedMoment B raw4750step0 raw4750step0Labels = mixedMoment B raw4750step1 raw4750step1Labels := by
      have ha : raw4750step1 = -raw4750step0 := by apply Matrix.ext; change ∀ i j, raw4750step1 i j = -(raw4750step0 i j); unfold raw4750step1 raw4750step0; decide +kernel
      have hl : raw4750step1Labels = raw4750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2009 node2009Labels := by rfl

def raw4751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4751 raw4751Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw4751 raw4751Labels = mixedMoment B raw4751step0 raw4751step0Labels := by
      have hz : ∀ j, raw4751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4751step0 = (fun i j => raw4751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4751step0 raw4751; decide +kernel
      have hl : raw4751step0Labels = raw4751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4751 raw4751Labels permutation346 hz
    mixedMoment B raw4751step0 raw4751step0Labels = mixedMoment B raw4751step1 raw4751step1Labels := by
      have ha : raw4751step1 = (fun i j => raw4751step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4751step1 raw4751step0; decide +kernel
      have hl : raw4751step1Labels = raw4751step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4751step0 raw4751step0Labels permutation139 permutation2
    mixedMoment B raw4751step1 raw4751step1Labels = mixedMoment B raw4751step2 raw4751step2Labels := by
      have ha : raw4751step2 = -raw4751step1 := by apply Matrix.ext; change ∀ i j, raw4751step2 i j = -(raw4751step1 i j); unfold raw4751step2 raw4751step1; decide +kernel
      have hl : raw4751step2Labels = raw4751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw4752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4752 raw4752Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw4752 raw4752Labels = mixedMoment B raw4752step0 raw4752step0Labels := by
      have hz : ∀ j, raw4752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4752step0 = (fun i j => raw4752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4752step0 raw4752; decide +kernel
      have hl : raw4752step0Labels = raw4752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4752 raw4752Labels permutation346 hz
    mixedMoment B raw4752step0 raw4752step0Labels = mixedMoment B raw4752step1 raw4752step1Labels := by
      have ha : raw4752step1 = (fun i j => raw4752step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4752step1 raw4752step0; decide +kernel
      have hl : raw4752step1Labels = raw4752step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4752step0 raw4752step0Labels permutation137 permutation2
    mixedMoment B raw4752step1 raw4752step1Labels = mixedMoment B raw4752step2 raw4752step2Labels := by
      have ha : raw4752step2 = -raw4752step1 := by apply Matrix.ext; change ∀ i j, raw4752step2 i j = -(raw4752step1 i j); unfold raw4752step2 raw4752step1; decide +kernel
      have hl : raw4752step2Labels = raw4752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw4753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw4753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4753 raw4753Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw4753 raw4753Labels = mixedMoment B raw4753step0 raw4753step0Labels := by
      have hz : ∀ j, raw4753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4753step0 = (fun i j => raw4753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4753step0 raw4753; decide +kernel
      have hl : raw4753step0Labels = raw4753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4753 raw4753Labels permutation346 hz
    mixedMoment B raw4753step0 raw4753step0Labels = mixedMoment B raw4753step1 raw4753step1Labels := by
      have ha : raw4753step1 = (fun i j => raw4753step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4753step1 raw4753step0; decide +kernel
      have hl : raw4753step1Labels = raw4753step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4753step0 raw4753step0Labels permutation40 permutation2
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw4754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4754 raw4754Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw4754 raw4754Labels = mixedMoment B raw4754step0 raw4754step0Labels := by
      have ha : raw4754step0 = (fun i j => raw4754 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4754step0 raw4754; decide +kernel
      have hl : raw4754step0Labels = raw4754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4754 raw4754Labels permutation640 permutation2
    mixedMoment B raw4754step0 raw4754step0Labels = mixedMoment B raw4754step1 raw4754step1Labels := by
      have ha : raw4754step1 = -raw4754step0 := by apply Matrix.ext; change ∀ i j, raw4754step1 i j = -(raw4754step0 i j); unfold raw4754step1 raw4754step0; decide +kernel
      have hl : raw4754step1Labels = raw4754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2009 node2009Labels := by rfl

def raw4755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4755step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4755 raw4755Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw4755 raw4755Labels = mixedMoment B raw4755step0 raw4755step0Labels := by
      have hz : ∀ j, raw4755 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4755step0 = (fun i j => raw4755 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4755step0 raw4755; decide +kernel
      have hl : raw4755step0Labels = raw4755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4755 raw4755Labels permutation346 hz
    mixedMoment B raw4755step0 raw4755step0Labels = mixedMoment B raw4755step1 raw4755step1Labels := by
      have ha : raw4755step1 = (fun i j => raw4755step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4755step1 raw4755step0; decide +kernel
      have hl : raw4755step1Labels = raw4755step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4755step0 raw4755step0Labels permutation145 permutation2
    mixedMoment B raw4755step1 raw4755step1Labels = mixedMoment B raw4755step2 raw4755step2Labels := by
      have ha : raw4755step2 = -raw4755step1 := by apply Matrix.ext; change ∀ i j, raw4755step2 i j = -(raw4755step1 i j); unfold raw4755step2 raw4755step1; decide +kernel
      have hl : raw4755step2Labels = raw4755step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2090 node2090Labels := by rfl

def raw4756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4756 raw4756Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw4756 raw4756Labels = mixedMoment B raw4756step0 raw4756step0Labels := by
      have hz : ∀ j, raw4756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4756step0 = (fun i j => raw4756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4756step0 raw4756; decide +kernel
      have hl : raw4756step0Labels = raw4756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4756 raw4756Labels permutation346 hz
    mixedMoment B raw4756step0 raw4756step0Labels = mixedMoment B raw4756step1 raw4756step1Labels := by
      have ha : raw4756step1 = (fun i j => raw4756step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4756step1 raw4756step0; decide +kernel
      have hl : raw4756step1Labels = raw4756step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4756step0 raw4756step0Labels permutation151 permutation2
    mixedMoment B raw4756step1 raw4756step1Labels = mixedMoment B raw4756step2 raw4756step2Labels := by
      have ha : raw4756step2 = -raw4756step1 := by apply Matrix.ext; change ∀ i j, raw4756step2 i j = -(raw4756step1 i j); unfold raw4756step2 raw4756step1; decide +kernel
      have hl : raw4756step2Labels = raw4756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2090 node2090Labels := by rfl

def raw4757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4757 raw4757Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw4757 raw4757Labels = mixedMoment B raw4757step0 raw4757step0Labels := by
      have hz : ∀ j, raw4757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4757step0 = (fun i j => raw4757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4757step0 raw4757; decide +kernel
      have hl : raw4757step0Labels = raw4757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4757 raw4757Labels permutation346 hz
    mixedMoment B raw4757step0 raw4757step0Labels = mixedMoment B raw4757step1 raw4757step1Labels := by
      have ha : raw4757step1 = (fun i j => raw4757step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4757step1 raw4757step0; decide +kernel
      have hl : raw4757step1Labels = raw4757step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4757step0 raw4757step0Labels permutation145 permutation2
    mixedMoment B raw4757step1 raw4757step1Labels = mixedMoment B raw4757step2 raw4757step2Labels := by
      have ha : raw4757step2 = -raw4757step1 := by apply Matrix.ext; change ∀ i j, raw4757step2 i j = -(raw4757step1 i j); unfold raw4757step2 raw4757step1; decide +kernel
      have hl : raw4757step2Labels = raw4757step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1022 node1022Labels := by rfl

def raw4758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4758 raw4758Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw4758 raw4758Labels = mixedMoment B raw4758step0 raw4758step0Labels := by
      have hz : ∀ j, raw4758 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4758step0 = (fun i j => raw4758 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4758step0 raw4758; decide +kernel
      have hl : raw4758step0Labels = raw4758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4758 raw4758Labels permutation265 hz
    mixedMoment B raw4758step0 raw4758step0Labels = mixedMoment B raw4758step1 raw4758step1Labels := by
      have ha : raw4758step1 = (fun i j => raw4758step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4758step1 raw4758step0; decide +kernel
      have hl : raw4758step1Labels = raw4758step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4758step0 raw4758step0Labels permutation145 permutation2
    mixedMoment B raw4758step1 raw4758step1Labels = mixedMoment B raw4758step2 raw4758step2Labels := by
      have ha : raw4758step2 = -raw4758step1 := by apply Matrix.ext; change ∀ i j, raw4758step2 i j = -(raw4758step1 i j); unfold raw4758step2 raw4758step1; decide +kernel
      have hl : raw4758step2Labels = raw4758step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2090 node2090Labels := by rfl

def raw4759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4759step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4759 raw4759Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw4759 raw4759Labels = mixedMoment B raw4759step0 raw4759step0Labels := by
      have hz : ∀ j, raw4759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4759step0 = (fun i j => raw4759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4759step0 raw4759; decide +kernel
      have hl : raw4759step0Labels = raw4759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4759 raw4759Labels permutation346 hz
    mixedMoment B raw4759step0 raw4759step0Labels = mixedMoment B raw4759step1 raw4759step1Labels := by
      have hz : ∀ j, raw4759step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4759step1 = (fun i j => raw4759step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4759step1 raw4759step0; decide +kernel
      have hl : raw4759step1Labels = raw4759step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4759step0 raw4759step0Labels permutation56 hz
    mixedMoment B raw4759step1 raw4759step1Labels = mixedMoment B raw4759step2 raw4759step2Labels := by
      have ha : raw4759step2 = (fun i j => raw4759step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4759step2 raw4759step1; decide +kernel
      have hl : raw4759step2Labels = raw4759step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4759step1 raw4759step1Labels permutation29 permutation2
    mixedMoment B raw4759step2 raw4759step2Labels = mixedMoment B raw4759step3 raw4759step3Labels := by
      have ha : raw4759step3 = -raw4759step2 := by apply Matrix.ext; change ∀ i j, raw4759step3 i j = -(raw4759step2 i j); unfold raw4759step3 raw4759step2; decide +kernel
      have hl : raw4759step3Labels = raw4759step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw4760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4760 raw4760Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw4760 raw4760Labels = mixedMoment B raw4760step0 raw4760step0Labels := by
      have hz : ∀ j, raw4760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4760step0 = (fun i j => raw4760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4760step0 raw4760; decide +kernel
      have hl : raw4760step0Labels = raw4760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4760 raw4760Labels permutation346 hz
    mixedMoment B raw4760step0 raw4760step0Labels = mixedMoment B raw4760step1 raw4760step1Labels := by
      have hz : ∀ j, raw4760step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4760step1 = (fun i j => raw4760step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4760step1 raw4760step0; decide +kernel
      have hl : raw4760step1Labels = raw4760step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4760step0 raw4760step0Labels permutation56 hz
    mixedMoment B raw4760step1 raw4760step1Labels = mixedMoment B raw4760step2 raw4760step2Labels := by
      have ha : raw4760step2 = (fun i j => raw4760step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4760step2 raw4760step1; decide +kernel
      have hl : raw4760step2Labels = raw4760step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4760step1 raw4760step1Labels permutation10 permutation2
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw4761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4761 raw4761Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw4761 raw4761Labels = mixedMoment B raw4761step0 raw4761step0Labels := by
      have hz : ∀ j, raw4761 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4761step0 = (fun i j => raw4761 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4761step0 raw4761; decide +kernel
      have hl : raw4761step0Labels = raw4761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4761 raw4761Labels permutation265 hz
    mixedMoment B raw4761step0 raw4761step0Labels = mixedMoment B raw4761step1 raw4761step1Labels := by
      have ha : raw4761step1 = (fun i j => raw4761step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4761step1 raw4761step0; decide +kernel
      have hl : raw4761step1Labels = raw4761step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4761step0 raw4761step0Labels permutation139 permutation2
    mixedMoment B raw4761step1 raw4761step1Labels = mixedMoment B raw4761step2 raw4761step2Labels := by
      have ha : raw4761step2 = -raw4761step1 := by apply Matrix.ext; change ∀ i j, raw4761step2 i j = -(raw4761step1 i j); unfold raw4761step2 raw4761step1; decide +kernel
      have hl : raw4761step2Labels = raw4761step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw4762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4762step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4762 raw4762Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw4762 raw4762Labels = mixedMoment B raw4762step0 raw4762step0Labels := by
      have hz : ∀ j, raw4762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4762step0 = (fun i j => raw4762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4762step0 raw4762; decide +kernel
      have hl : raw4762step0Labels = raw4762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4762 raw4762Labels permutation346 hz
    mixedMoment B raw4762step0 raw4762step0Labels = mixedMoment B raw4762step1 raw4762step1Labels := by
      have hz : ∀ j, raw4762step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4762step1 = (fun i j => raw4762step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4762step1 raw4762step0; decide +kernel
      have hl : raw4762step1Labels = raw4762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4762step0 raw4762step0Labels permutation56 hz
    mixedMoment B raw4762step1 raw4762step1Labels = mixedMoment B raw4762step2 raw4762step2Labels := by
      have ha : raw4762step2 = (fun i j => raw4762step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4762step2 raw4762step1; decide +kernel
      have hl : raw4762step2Labels = raw4762step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4762step1 raw4762step1Labels permutation31 permutation2
    mixedMoment B raw4762step2 raw4762step2Labels = mixedMoment B raw4762step3 raw4762step3Labels := by
      have ha : raw4762step3 = -raw4762step2 := by apply Matrix.ext; change ∀ i j, raw4762step3 i j = -(raw4762step2 i j); unfold raw4762step3 raw4762step2; decide +kernel
      have hl : raw4762step3Labels = raw4762step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw4763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4763 raw4763Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw4763 raw4763Labels = mixedMoment B raw4763step0 raw4763step0Labels := by
      have hz : ∀ j, raw4763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4763step0 = (fun i j => raw4763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4763step0 raw4763; decide +kernel
      have hl : raw4763step0Labels = raw4763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4763 raw4763Labels permutation346 hz
    mixedMoment B raw4763step0 raw4763step0Labels = mixedMoment B raw4763step1 raw4763step1Labels := by
      have hz : ∀ j, raw4763step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4763step1 = (fun i j => raw4763step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4763step1 raw4763step0; decide +kernel
      have hl : raw4763step1Labels = raw4763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4763step0 raw4763step0Labels permutation56 hz
    mixedMoment B raw4763step1 raw4763step1Labels = mixedMoment B raw4763step2 raw4763step2Labels := by
      have ha : raw4763step2 = (fun i j => raw4763step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4763step2 raw4763step1; decide +kernel
      have hl : raw4763step2Labels = raw4763step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4763step1 raw4763step1Labels permutation31 permutation2
    mixedMoment B raw4763step2 raw4763step2Labels = mixedMoment B raw4763step3 raw4763step3Labels := by
      have ha : raw4763step3 = -raw4763step2 := by apply Matrix.ext; change ∀ i j, raw4763step3 i j = -(raw4763step2 i j); unfold raw4763step3 raw4763step2; decide +kernel
      have hl : raw4763step3Labels = raw4763step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw4764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4764 raw4764Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw4764 raw4764Labels = mixedMoment B raw4764step0 raw4764step0Labels := by
      have hz : ∀ j, raw4764 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4764step0 = (fun i j => raw4764 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4764step0 raw4764; decide +kernel
      have hl : raw4764step0Labels = raw4764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4764 raw4764Labels permutation265 hz
    mixedMoment B raw4764step0 raw4764step0Labels = mixedMoment B raw4764step1 raw4764step1Labels := by
      have ha : raw4764step1 = (fun i j => raw4764step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4764step1 raw4764step0; decide +kernel
      have hl : raw4764step1Labels = raw4764step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4764step0 raw4764step0Labels permutation145 permutation2
    mixedMoment B raw4764step1 raw4764step1Labels = mixedMoment B raw4764step2 raw4764step2Labels := by
      have ha : raw4764step2 = -raw4764step1 := by apply Matrix.ext; change ∀ i j, raw4764step2 i j = -(raw4764step1 i j); unfold raw4764step2 raw4764step1; decide +kernel
      have hl : raw4764step2Labels = raw4764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1022 node1022Labels := by rfl

def raw4765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4765step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4765 raw4765Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw4765 raw4765Labels = mixedMoment B raw4765step0 raw4765step0Labels := by
      have hz : ∀ j, raw4765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4765step0 = (fun i j => raw4765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4765step0 raw4765; decide +kernel
      have hl : raw4765step0Labels = raw4765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4765 raw4765Labels permutation346 hz
    mixedMoment B raw4765step0 raw4765step0Labels = mixedMoment B raw4765step1 raw4765step1Labels := by
      have hz : ∀ j, raw4765step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4765step1 = (fun i j => raw4765step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4765step1 raw4765step0; decide +kernel
      have hl : raw4765step1Labels = raw4765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4765step0 raw4765step0Labels permutation56 hz
    mixedMoment B raw4765step1 raw4765step1Labels = mixedMoment B raw4765step2 raw4765step2Labels := by
      have ha : raw4765step2 = (fun i j => raw4765step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4765step2 raw4765step1; decide +kernel
      have hl : raw4765step2Labels = raw4765step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4765step1 raw4765step1Labels permutation29 permutation2
    mixedMoment B raw4765step2 raw4765step2Labels = mixedMoment B raw4765step3 raw4765step3Labels := by
      have ha : raw4765step3 = -raw4765step2 := by apply Matrix.ext; change ∀ i j, raw4765step3 i j = -(raw4765step2 i j); unfold raw4765step3 raw4765step2; decide +kernel
      have hl : raw4765step3Labels = raw4765step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw4766 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4766 raw4766Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw4766 raw4766Labels = mixedMoment B raw4766step0 raw4766step0Labels := by
      have hz : ∀ j, raw4766 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4766step0 = (fun i j => raw4766 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4766step0 raw4766; decide +kernel
      have hl : raw4766step0Labels = raw4766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4766 raw4766Labels permutation265 hz
    mixedMoment B raw4766step0 raw4766step0Labels = mixedMoment B raw4766step1 raw4766step1Labels := by
      have ha : raw4766step1 = (fun i j => raw4766step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4766step1 raw4766step0; decide +kernel
      have hl : raw4766step1Labels = raw4766step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4766step0 raw4766step0Labels permutation137 permutation2
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw4767 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw4767step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4767step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4767step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4767step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4767step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4767 raw4767Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw4767 raw4767Labels = mixedMoment B raw4767step0 raw4767step0Labels := by
      have hz : ∀ j, raw4767 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4767step0 = (fun i j => raw4767 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4767step0 raw4767; decide +kernel
      have hl : raw4767step0Labels = raw4767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4767 raw4767Labels permutation520 hz
    mixedMoment B raw4767step0 raw4767step0Labels = mixedMoment B raw4767step1 raw4767step1Labels := by
      have hz : ∀ j, raw4767step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4767step1 = (fun i j => raw4767step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4767step1 raw4767step0; decide +kernel
      have hl : raw4767step1Labels = raw4767step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4767step0 raw4767step0Labels permutation80 hz
    mixedMoment B raw4767step1 raw4767step1Labels = mixedMoment B raw4767step2 raw4767step2Labels := by
      have hz : ∀ j, raw4767step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4767step2 = (fun i j => raw4767step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4767step2 raw4767step1; decide +kernel
      have hl : raw4767step2Labels = raw4767step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4767step1 raw4767step1Labels permutation14 hz
    mixedMoment B raw4767step2 raw4767step2Labels = mixedMoment B raw4767step3 raw4767step3Labels := by
      have ha : raw4767step3 = (fun i j => raw4767step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4767step3 raw4767step2; decide +kernel
      have hl : raw4767step3Labels = raw4767step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4767step2 raw4767step2Labels permutation7 permutation7
    mixedMoment B raw4767step3 raw4767step3Labels = mixedMoment B raw4767step4 raw4767step4Labels := by
      have ha : raw4767step4 = -raw4767step3 := by apply Matrix.ext; change ∀ i j, raw4767step4 i j = -(raw4767step3 i j); unfold raw4767step4 raw4767step3; decide +kernel
      have hl : raw4767step4Labels = raw4767step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4767step4 raw4767step4Labels = mixedMoment B raw4767step5 raw4767step5Labels := by
      have ha : raw4767step5 = raw4767step4 := by apply Matrix.ext; unfold raw4767step5 raw4767step4; decide +kernel
      have hl : raw4767step4Labels = labelEmbedding10 ∘ raw4767step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4767step4 raw4767step4Labels raw4767step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw4768 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4768step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4768 raw4768Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw4768 raw4768Labels = mixedMoment B raw4768step0 raw4768step0Labels := by
      have hz : ∀ j, raw4768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4768step0 = (fun i j => raw4768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4768step0 raw4768; decide +kernel
      have hl : raw4768step0Labels = raw4768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4768 raw4768Labels permutation346 hz
    mixedMoment B raw4768step0 raw4768step0Labels = mixedMoment B raw4768step1 raw4768step1Labels := by
      have hz : ∀ j, raw4768step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4768step1 = (fun i j => raw4768step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4768step1 raw4768step0; decide +kernel
      have hl : raw4768step1Labels = raw4768step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4768step0 raw4768step0Labels permutation56 hz
    mixedMoment B raw4768step1 raw4768step1Labels = mixedMoment B raw4768step2 raw4768step2Labels := by
      have ha : raw4768step2 = (fun i j => raw4768step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4768step2 raw4768step1; decide +kernel
      have hl : raw4768step2Labels = raw4768step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4768step1 raw4768step1Labels permutation29 permutation2
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw4769 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4769 raw4769Labels = mixedMoment B node4830 node4830Labels := by
  calc
    mixedMoment B raw4769 raw4769Labels = mixedMoment B raw4769step0 raw4769step0Labels := by
      have ha : raw4769step0 = (fun i j => raw4769 (permutation632 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4769step0 raw4769; decide +kernel
      have hl : raw4769step0Labels = raw4769Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4769 raw4769Labels permutation632 permutation2
    _ = mixedMoment B node4830 node4830Labels := by rfl

def raw4770 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4770step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4770step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4770step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4770step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4770step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4770step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4770 raw4770Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw4770 raw4770Labels = mixedMoment B raw4770step0 raw4770step0Labels := by
      have hz : ∀ j, raw4770 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4770step0 = (fun i j => raw4770 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4770step0 raw4770; decide +kernel
      have hl : raw4770step0Labels = raw4770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4770 raw4770Labels permutation520 hz
    mixedMoment B raw4770step0 raw4770step0Labels = mixedMoment B raw4770step1 raw4770step1Labels := by
      have hz : ∀ j, raw4770step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4770step1 = (fun i j => raw4770step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4770step1 raw4770step0; decide +kernel
      have hl : raw4770step1Labels = raw4770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4770step0 raw4770step0Labels permutation80 hz
    mixedMoment B raw4770step1 raw4770step1Labels = mixedMoment B raw4770step2 raw4770step2Labels := by
      have ha : raw4770step2 = (fun i j => raw4770step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4770step2 raw4770step1; decide +kernel
      have hl : raw4770step2Labels = raw4770step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4770step1 raw4770step1Labels permutation29 permutation7
    mixedMoment B raw4770step2 raw4770step2Labels = mixedMoment B raw4770step3 raw4770step3Labels := by
      have ha : raw4770step3 = -raw4770step2 := by apply Matrix.ext; change ∀ i j, raw4770step3 i j = -(raw4770step2 i j); unfold raw4770step3 raw4770step2; decide +kernel
      have hl : raw4770step3Labels = raw4770step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4770step3 raw4770step3Labels = mixedMoment B raw4770step4 raw4770step4Labels := by
      have ha : raw4770step4 = raw4770step3 := by apply Matrix.ext; unfold raw4770step4 raw4770step3; decide +kernel
      have hl : raw4770step3Labels = labelEmbedding10 ∘ raw4770step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4770step3 raw4770step3Labels raw4770step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw4771 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4771 raw4771Labels = mixedMoment B node4494 node4494Labels := by
  calc
    mixedMoment B raw4771 raw4771Labels = mixedMoment B raw4771step0 raw4771step0Labels := by
      have hz : ∀ j, raw4771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4771step0 = (fun i j => raw4771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4771step0 raw4771; decide +kernel
      have hl : raw4771step0Labels = raw4771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4771 raw4771Labels permutation346 hz
    mixedMoment B raw4771step0 raw4771step0Labels = mixedMoment B raw4771step1 raw4771step1Labels := by
      have ha : raw4771step1 = (fun i j => raw4771step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4771step1 raw4771step0; decide +kernel
      have hl : raw4771step1Labels = raw4771step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4771step0 raw4771step0Labels permutation137 permutation2
    _ = mixedMoment B node4494 node4494Labels := by rfl

def raw4772 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4772 raw4772Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw4772 raw4772Labels = mixedMoment B raw4772step0 raw4772step0Labels := by
      have hz : ∀ j, raw4772 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4772step0 = (fun i j => raw4772 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4772step0 raw4772; decide +kernel
      have hl : raw4772step0Labels = raw4772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4772 raw4772Labels permutation265 hz
    mixedMoment B raw4772step0 raw4772step0Labels = mixedMoment B raw4772step1 raw4772step1Labels := by
      have ha : raw4772step1 = (fun i j => raw4772step0 (permutation138 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4772step1 raw4772step0; decide +kernel
      have hl : raw4772step1Labels = raw4772step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4772step0 raw4772step0Labels permutation138 permutation2
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw4773 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw4773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw4773step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4773step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4773step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4773step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4773step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4773 raw4773Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw4773 raw4773Labels = mixedMoment B raw4773step0 raw4773step0Labels := by
      have hz : ∀ j, raw4773 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4773step0 = (fun i j => raw4773 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4773step0 raw4773; decide +kernel
      have hl : raw4773step0Labels = raw4773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4773 raw4773Labels permutation520 hz
    mixedMoment B raw4773step0 raw4773step0Labels = mixedMoment B raw4773step1 raw4773step1Labels := by
      have hz : ∀ j, raw4773step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4773step1 = (fun i j => raw4773step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4773step1 raw4773step0; decide +kernel
      have hl : raw4773step1Labels = raw4773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4773step0 raw4773step0Labels permutation80 hz
    mixedMoment B raw4773step1 raw4773step1Labels = mixedMoment B raw4773step2 raw4773step2Labels := by
      have hz : ∀ j, raw4773step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4773step2 = (fun i j => raw4773step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4773step2 raw4773step1; decide +kernel
      have hl : raw4773step2Labels = raw4773step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4773step1 raw4773step1Labels permutation14 hz
    mixedMoment B raw4773step2 raw4773step2Labels = mixedMoment B raw4773step3 raw4773step3Labels := by
      have ha : raw4773step3 = (fun i j => raw4773step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4773step3 raw4773step2; decide +kernel
      have hl : raw4773step3Labels = raw4773step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4773step2 raw4773step2Labels permutation7 permutation7
    mixedMoment B raw4773step3 raw4773step3Labels = mixedMoment B raw4773step4 raw4773step4Labels := by
      have ha : raw4773step4 = -raw4773step3 := by apply Matrix.ext; change ∀ i j, raw4773step4 i j = -(raw4773step3 i j); unfold raw4773step4 raw4773step3; decide +kernel
      have hl : raw4773step4Labels = raw4773step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4773step4 raw4773step4Labels = mixedMoment B raw4773step5 raw4773step5Labels := by
      have ha : raw4773step5 = raw4773step4 := by apply Matrix.ext; unfold raw4773step5 raw4773step4; decide +kernel
      have hl : raw4773step4Labels = labelEmbedding10 ∘ raw4773step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4773step4 raw4773step4Labels raw4773step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw4774 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4774 raw4774Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw4774 raw4774Labels = mixedMoment B raw4774step0 raw4774step0Labels := by
      have hz : ∀ j, raw4774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4774step0 = (fun i j => raw4774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4774step0 raw4774; decide +kernel
      have hl : raw4774step0Labels = raw4774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4774 raw4774Labels permutation346 hz
    mixedMoment B raw4774step0 raw4774step0Labels = mixedMoment B raw4774step1 raw4774step1Labels := by
      have hz : ∀ j, raw4774step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4774step1 = (fun i j => raw4774step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4774step1 raw4774step0; decide +kernel
      have hl : raw4774step1Labels = raw4774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4774step0 raw4774step0Labels permutation56 hz
    mixedMoment B raw4774step1 raw4774step1Labels = mixedMoment B raw4774step2 raw4774step2Labels := by
      have ha : raw4774step2 = (fun i j => raw4774step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4774step2 raw4774step1; decide +kernel
      have hl : raw4774step2Labels = raw4774step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4774step1 raw4774step1Labels permutation30 permutation2
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw4775 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4775step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4775 raw4775Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw4775 raw4775Labels = mixedMoment B raw4775step0 raw4775step0Labels := by
      have hz : ∀ j, raw4775 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4775step0 = (fun i j => raw4775 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4775step0 raw4775; decide +kernel
      have hl : raw4775step0Labels = raw4775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4775 raw4775Labels permutation265 hz
    mixedMoment B raw4775step0 raw4775step0Labels = mixedMoment B raw4775step1 raw4775step1Labels := by
      have ha : raw4775step1 = (fun i j => raw4775step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4775step1 raw4775step0; decide +kernel
      have hl : raw4775step1Labels = raw4775step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4775step0 raw4775step0Labels permutation32 permutation6
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw4776 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4776step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4776step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4776step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4776step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw4776step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4776 raw4776Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw4776 raw4776Labels = mixedMoment B raw4776step0 raw4776step0Labels := by
      have hz : ∀ j, raw4776 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4776step0 = (fun i j => raw4776 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4776step0 raw4776; decide +kernel
      have hl : raw4776step0Labels = raw4776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4776 raw4776Labels permutation520 hz
    mixedMoment B raw4776step0 raw4776step0Labels = mixedMoment B raw4776step1 raw4776step1Labels := by
      have hz : ∀ j, raw4776step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4776step1 = (fun i j => raw4776step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4776step1 raw4776step0; decide +kernel
      have hl : raw4776step1Labels = raw4776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4776step0 raw4776step0Labels permutation80 hz
    mixedMoment B raw4776step1 raw4776step1Labels = mixedMoment B raw4776step2 raw4776step2Labels := by
      have hz : ∀ j, raw4776step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4776step2 = (fun i j => raw4776step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4776step2 raw4776step1; decide +kernel
      have hl : raw4776step2Labels = raw4776step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4776step1 raw4776step1Labels permutation14 hz
    mixedMoment B raw4776step2 raw4776step2Labels = mixedMoment B raw4776step3 raw4776step3Labels := by
      have ha : raw4776step3 = (fun i j => raw4776step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4776step3 raw4776step2; decide +kernel
      have hl : raw4776step3Labels = raw4776step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4776step2 raw4776step2Labels permutation2 permutation6
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw4777 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4777step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4777 raw4777Labels = mixedMoment B node1451 node1451Labels := by
  calc
    mixedMoment B raw4777 raw4777Labels = mixedMoment B raw4777step0 raw4777step0Labels := by
      have hz : ∀ j, raw4777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4777step0 = (fun i j => raw4777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4777step0 raw4777; decide +kernel
      have hl : raw4777step0Labels = raw4777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4777 raw4777Labels permutation346 hz
    mixedMoment B raw4777step0 raw4777step0Labels = mixedMoment B raw4777step1 raw4777step1Labels := by
      have hz : ∀ j, raw4777step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4777step1 = (fun i j => raw4777step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4777step1 raw4777step0; decide +kernel
      have hl : raw4777step1Labels = raw4777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4777step0 raw4777step0Labels permutation56 hz
    mixedMoment B raw4777step1 raw4777step1Labels = mixedMoment B raw4777step2 raw4777step2Labels := by
      have ha : raw4777step2 = (fun i j => raw4777step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4777step2 raw4777step1; decide +kernel
      have hl : raw4777step2Labels = raw4777step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4777step1 raw4777step1Labels permutation29 permutation3
    _ = mixedMoment B node1451 node1451Labels := by rfl

def raw4778 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4778 raw4778Labels = mixedMoment B node2707 node2707Labels := by
  calc
    mixedMoment B raw4778 raw4778Labels = mixedMoment B raw4778step0 raw4778step0Labels := by
      have ha : raw4778step0 = (fun i j => raw4778 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4778step0 raw4778; decide +kernel
      have hl : raw4778step0Labels = raw4778Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4778 raw4778Labels permutation176 permutation6
    _ = mixedMoment B node2707 node2707Labels := by rfl

def raw4779 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4779step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4779 raw4779Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw4779 raw4779Labels = mixedMoment B raw4779step0 raw4779step0Labels := by
      have hz : ∀ j, raw4779 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4779step0 = (fun i j => raw4779 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4779step0 raw4779; decide +kernel
      have hl : raw4779step0Labels = raw4779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4779 raw4779Labels permutation520 hz
    mixedMoment B raw4779step0 raw4779step0Labels = mixedMoment B raw4779step1 raw4779step1Labels := by
      have hz : ∀ j, raw4779step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4779step1 = (fun i j => raw4779step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4779step1 raw4779step0; decide +kernel
      have hl : raw4779step1Labels = raw4779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4779step0 raw4779step0Labels permutation80 hz
    mixedMoment B raw4779step1 raw4779step1Labels = mixedMoment B raw4779step2 raw4779step2Labels := by
      have ha : raw4779step2 = (fun i j => raw4779step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4779step2 raw4779step1; decide +kernel
      have hl : raw4779step2Labels = raw4779step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4779step1 raw4779step1Labels permutation8 permutation6
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw4780 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw4780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4780 raw4780Labels = mixedMoment B node1435 node1435Labels := by
  calc
    mixedMoment B raw4780 raw4780Labels = mixedMoment B raw4780step0 raw4780step0Labels := by
      have hz : ∀ j, raw4780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4780step0 = (fun i j => raw4780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4780step0 raw4780; decide +kernel
      have hl : raw4780step0Labels = raw4780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4780 raw4780Labels permutation346 hz
    mixedMoment B raw4780step0 raw4780step0Labels = mixedMoment B raw4780step1 raw4780step1Labels := by
      have ha : raw4780step1 = (fun i j => raw4780step0 (permutation128 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4780step1 raw4780step0; decide +kernel
      have hl : raw4780step1Labels = raw4780step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4780step0 raw4780step0Labels permutation128 permutation3
    _ = mixedMoment B node1435 node1435Labels := by rfl

def raw4781 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4781 raw4781Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw4781 raw4781Labels = mixedMoment B raw4781step0 raw4781step0Labels := by
      have hz : ∀ j, raw4781 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4781step0 = (fun i j => raw4781 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4781step0 raw4781; decide +kernel
      have hl : raw4781step0Labels = raw4781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4781 raw4781Labels permutation265 hz
    mixedMoment B raw4781step0 raw4781step0Labels = mixedMoment B raw4781step1 raw4781step1Labels := by
      have ha : raw4781step1 = (fun i j => raw4781step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4781step1 raw4781step0; decide +kernel
      have hl : raw4781step1Labels = raw4781step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4781step0 raw4781step0Labels permutation34 permutation6
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw4782 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4782step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4782step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw4782step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4782step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw4782step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4782 raw4782Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw4782 raw4782Labels = mixedMoment B raw4782step0 raw4782step0Labels := by
      have hz : ∀ j, raw4782 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4782step0 = (fun i j => raw4782 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4782step0 raw4782; decide +kernel
      have hl : raw4782step0Labels = raw4782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4782 raw4782Labels permutation520 hz
    mixedMoment B raw4782step0 raw4782step0Labels = mixedMoment B raw4782step1 raw4782step1Labels := by
      have hz : ∀ j, raw4782step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4782step1 = (fun i j => raw4782step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4782step1 raw4782step0; decide +kernel
      have hl : raw4782step1Labels = raw4782step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4782step0 raw4782step0Labels permutation80 hz
    mixedMoment B raw4782step1 raw4782step1Labels = mixedMoment B raw4782step2 raw4782step2Labels := by
      have hz : ∀ j, raw4782step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4782step2 = (fun i j => raw4782step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4782step2 raw4782step1; decide +kernel
      have hl : raw4782step2Labels = raw4782step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4782step1 raw4782step1Labels permutation14 hz
    mixedMoment B raw4782step2 raw4782step2Labels = mixedMoment B raw4782step3 raw4782step3Labels := by
      have ha : raw4782step3 = (fun i j => raw4782step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4782step3 raw4782step2; decide +kernel
      have hl : raw4782step3Labels = raw4782step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4782step2 raw4782step2Labels permutation2 permutation6
    _ = mixedMoment B node2778 node2778Labels := by rfl

def raw4783 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4783step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4783step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4783step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4783 raw4783Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw4783 raw4783Labels = mixedMoment B raw4783step0 raw4783step0Labels := by
      have hz : ∀ j, raw4783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4783step0 = (fun i j => raw4783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4783step0 raw4783; decide +kernel
      have hl : raw4783step0Labels = raw4783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4783 raw4783Labels permutation346 hz
    mixedMoment B raw4783step0 raw4783step0Labels = mixedMoment B raw4783step1 raw4783step1Labels := by
      have hz : ∀ j, raw4783step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4783step1 = (fun i j => raw4783step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4783step1 raw4783step0; decide +kernel
      have hl : raw4783step1Labels = raw4783step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4783step0 raw4783step0Labels permutation56 hz
    mixedMoment B raw4783step1 raw4783step1Labels = mixedMoment B raw4783step2 raw4783step2Labels := by
      have ha : raw4783step2 = (fun i j => raw4783step1 (permutation27 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4783step2 raw4783step1; decide +kernel
      have hl : raw4783step2Labels = raw4783step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4783step1 raw4783step1Labels permutation27 permutation3
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw4784 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4784step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4784 raw4784Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw4784 raw4784Labels = mixedMoment B raw4784step0 raw4784step0Labels := by
      have hz : ∀ j, raw4784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4784step0 = (fun i j => raw4784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4784step0 raw4784; decide +kernel
      have hl : raw4784step0Labels = raw4784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4784 raw4784Labels permutation346 hz
    mixedMoment B raw4784step0 raw4784step0Labels = mixedMoment B raw4784step1 raw4784step1Labels := by
      have ha : raw4784step1 = (fun i j => raw4784step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4784step1 raw4784step0; decide +kernel
      have hl : raw4784step1Labels = raw4784step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4784step0 raw4784step0Labels permutation137 permutation7
    mixedMoment B raw4784step1 raw4784step1Labels = mixedMoment B raw4784step2 raw4784step2Labels := by
      have ha : raw4784step2 = -raw4784step1 := by apply Matrix.ext; change ∀ i j, raw4784step2 i j = -(raw4784step1 i j); unfold raw4784step2 raw4784step1; decide +kernel
      have hl : raw4784step2Labels = raw4784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4784step2 raw4784step2Labels = mixedMoment B raw4784step3 raw4784step3Labels := by
      have ha : raw4784step3 = raw4784step2 := by apply Matrix.ext; unfold raw4784step3 raw4784step2; decide +kernel
      have hl : raw4784step2Labels = labelEmbedding1 ∘ raw4784step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4784step2 raw4784step2Labels raw4784step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw4785 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4785step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4785step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4785step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4785step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4785step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4785 raw4785Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw4785 raw4785Labels = mixedMoment B raw4785step0 raw4785step0Labels := by
      have hz : ∀ j, raw4785 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4785step0 = (fun i j => raw4785 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4785step0 raw4785; decide +kernel
      have hl : raw4785step0Labels = raw4785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4785 raw4785Labels permutation265 hz
    mixedMoment B raw4785step0 raw4785step0Labels = mixedMoment B raw4785step1 raw4785step1Labels := by
      have ha : raw4785step1 = (fun i j => raw4785step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4785step1 raw4785step0; decide +kernel
      have hl : raw4785step1Labels = raw4785step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4785step0 raw4785step0Labels permutation137 permutation7
    mixedMoment B raw4785step1 raw4785step1Labels = mixedMoment B raw4785step2 raw4785step2Labels := by
      have ha : raw4785step2 = -raw4785step1 := by apply Matrix.ext; change ∀ i j, raw4785step2 i j = -(raw4785step1 i j); unfold raw4785step2 raw4785step1; decide +kernel
      have hl : raw4785step2Labels = raw4785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4785step2 raw4785step2Labels = mixedMoment B raw4785step3 raw4785step3Labels := by
      have ha : raw4785step3 = raw4785step2 := by apply Matrix.ext; unfold raw4785step3 raw4785step2; decide +kernel
      have hl : raw4785step2Labels = labelEmbedding1 ∘ raw4785step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4785step2 raw4785step2Labels raw4785step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw4786 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4786step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4786step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4786step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4786step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4786step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw4786step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4786step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4786step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4786step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4786step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4786 raw4786Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw4786 raw4786Labels = mixedMoment B raw4786step0 raw4786step0Labels := by
      have hz : ∀ j, raw4786 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4786step0 = (fun i j => raw4786 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4786step0 raw4786; decide +kernel
      have hl : raw4786step0Labels = raw4786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4786 raw4786Labels permutation520 hz
    mixedMoment B raw4786step0 raw4786step0Labels = mixedMoment B raw4786step1 raw4786step1Labels := by
      have hz : ∀ j, raw4786step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4786step1 = (fun i j => raw4786step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4786step1 raw4786step0; decide +kernel
      have hl : raw4786step1Labels = raw4786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4786step0 raw4786step0Labels permutation80 hz
    mixedMoment B raw4786step1 raw4786step1Labels = mixedMoment B raw4786step2 raw4786step2Labels := by
      have hz : ∀ j, raw4786step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4786step2 = (fun i j => raw4786step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4786step2 raw4786step1; decide +kernel
      have hl : raw4786step2Labels = raw4786step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4786step1 raw4786step1Labels permutation14 hz
    mixedMoment B raw4786step2 raw4786step2Labels = mixedMoment B raw4786step3 raw4786step3Labels := by
      have ha : raw4786step3 = (fun i j => raw4786step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4786step3 raw4786step2; decide +kernel
      have hl : raw4786step3Labels = raw4786step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4786step2 raw4786step2Labels permutation7 permutation7
    mixedMoment B raw4786step3 raw4786step3Labels = mixedMoment B raw4786step4 raw4786step4Labels := by
      have ha : raw4786step4 = -raw4786step3 := by apply Matrix.ext; change ∀ i j, raw4786step4 i j = -(raw4786step3 i j); unfold raw4786step4 raw4786step3; decide +kernel
      have hl : raw4786step4Labels = raw4786step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4786step4 raw4786step4Labels = mixedMoment B raw4786step5 raw4786step5Labels := by
      have ha : raw4786step5 = raw4786step4 := by apply Matrix.ext; unfold raw4786step5 raw4786step4; decide +kernel
      have hl : raw4786step4Labels = labelEmbedding1 ∘ raw4786step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4786step4 raw4786step4Labels raw4786step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2268 node2268Labels := by rfl

def raw4787 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4787step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4787step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4787step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4787step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4787step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4787step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4787 raw4787Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw4787 raw4787Labels = mixedMoment B raw4787step0 raw4787step0Labels := by
      have hz : ∀ j, raw4787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4787step0 = (fun i j => raw4787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4787step0 raw4787; decide +kernel
      have hl : raw4787step0Labels = raw4787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4787 raw4787Labels permutation346 hz
    mixedMoment B raw4787step0 raw4787step0Labels = mixedMoment B raw4787step1 raw4787step1Labels := by
      have hz : ∀ j, raw4787step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4787step1 = (fun i j => raw4787step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4787step1 raw4787step0; decide +kernel
      have hl : raw4787step1Labels = raw4787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4787step0 raw4787step0Labels permutation56 hz
    mixedMoment B raw4787step1 raw4787step1Labels = mixedMoment B raw4787step2 raw4787step2Labels := by
      have ha : raw4787step2 = (fun i j => raw4787step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4787step2 raw4787step1; decide +kernel
      have hl : raw4787step2Labels = raw4787step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4787step1 raw4787step1Labels permutation29 permutation7
    mixedMoment B raw4787step2 raw4787step2Labels = mixedMoment B raw4787step3 raw4787step3Labels := by
      have ha : raw4787step3 = -raw4787step2 := by apply Matrix.ext; change ∀ i j, raw4787step3 i j = -(raw4787step2 i j); unfold raw4787step3 raw4787step2; decide +kernel
      have hl : raw4787step3Labels = raw4787step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4787step3 raw4787step3Labels = mixedMoment B raw4787step4 raw4787step4Labels := by
      have ha : raw4787step4 = raw4787step3 := by apply Matrix.ext; unfold raw4787step4 raw4787step3; decide +kernel
      have hl : raw4787step3Labels = labelEmbedding1 ∘ raw4787step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4787step3 raw4787step3Labels raw4787step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw4788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw4788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4788step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4788step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4788 raw4788Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw4788 raw4788Labels = mixedMoment B raw4788step0 raw4788step0Labels := by
      have hz : ∀ j, raw4788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4788step0 = (fun i j => raw4788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4788step0 raw4788; decide +kernel
      have hl : raw4788step0Labels = raw4788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4788 raw4788Labels permutation346 hz
    mixedMoment B raw4788step0 raw4788step0Labels = mixedMoment B raw4788step1 raw4788step1Labels := by
      have ha : raw4788step1 = (fun i j => raw4788step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4788step1 raw4788step0; decide +kernel
      have hl : raw4788step1Labels = raw4788step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4788step0 raw4788step0Labels permutation137 permutation7
    mixedMoment B raw4788step1 raw4788step1Labels = mixedMoment B raw4788step2 raw4788step2Labels := by
      have ha : raw4788step2 = -raw4788step1 := by apply Matrix.ext; change ∀ i j, raw4788step2 i j = -(raw4788step1 i j); unfold raw4788step2 raw4788step1; decide +kernel
      have hl : raw4788step2Labels = raw4788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4788step2 raw4788step2Labels = mixedMoment B raw4788step3 raw4788step3Labels := by
      have ha : raw4788step3 = raw4788step2 := by apply Matrix.ext; unfold raw4788step3 raw4788step2; decide +kernel
      have hl : raw4788step2Labels = labelEmbedding1 ∘ raw4788step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4788step2 raw4788step2Labels raw4788step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2235 node2235Labels := by rfl

def raw4789 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4789step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4789step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4789step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4789 raw4789Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw4789 raw4789Labels = mixedMoment B raw4789step0 raw4789step0Labels := by
      have ha : raw4789step0 = (fun i j => raw4789 (permutation632 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4789step0 raw4789; decide +kernel
      have hl : raw4789step0Labels = raw4789Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4789 raw4789Labels permutation632 permutation7
    mixedMoment B raw4789step0 raw4789step0Labels = mixedMoment B raw4789step1 raw4789step1Labels := by
      have ha : raw4789step1 = -raw4789step0 := by apply Matrix.ext; change ∀ i j, raw4789step1 i j = -(raw4789step0 i j); unfold raw4789step1 raw4789step0; decide +kernel
      have hl : raw4789step1Labels = raw4789step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4789step1 raw4789step1Labels = mixedMoment B raw4789step2 raw4789step2Labels := by
      have ha : raw4789step2 = raw4789step1 := by apply Matrix.ext; unfold raw4789step2 raw4789step1; decide +kernel
      have hl : raw4789step1Labels = labelEmbedding1 ∘ raw4789step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4789step1 raw4789step1Labels raw4789step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2187 node2187Labels := by rfl

def raw4790 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4790step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4790step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4790step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4790step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4790step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4790 raw4790Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw4790 raw4790Labels = mixedMoment B raw4790step0 raw4790step0Labels := by
      have hz : ∀ j, raw4790 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4790step0 = (fun i j => raw4790 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4790step0 raw4790; decide +kernel
      have hl : raw4790step0Labels = raw4790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4790 raw4790Labels permutation520 hz
    mixedMoment B raw4790step0 raw4790step0Labels = mixedMoment B raw4790step1 raw4790step1Labels := by
      have hz : ∀ j, raw4790step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4790step1 = (fun i j => raw4790step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4790step1 raw4790step0; decide +kernel
      have hl : raw4790step1Labels = raw4790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4790step0 raw4790step0Labels permutation80 hz
    mixedMoment B raw4790step1 raw4790step1Labels = mixedMoment B raw4790step2 raw4790step2Labels := by
      have ha : raw4790step2 = (fun i j => raw4790step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4790step2 raw4790step1; decide +kernel
      have hl : raw4790step2Labels = raw4790step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4790step1 raw4790step1Labels permutation29 permutation7
    mixedMoment B raw4790step2 raw4790step2Labels = mixedMoment B raw4790step3 raw4790step3Labels := by
      have ha : raw4790step3 = -raw4790step2 := by apply Matrix.ext; change ∀ i j, raw4790step3 i j = -(raw4790step2 i j); unfold raw4790step3 raw4790step2; decide +kernel
      have hl : raw4790step3Labels = raw4790step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4790step3 raw4790step3Labels = mixedMoment B raw4790step4 raw4790step4Labels := by
      have ha : raw4790step4 = raw4790step3 := by apply Matrix.ext; unfold raw4790step4 raw4790step3; decide +kernel
      have hl : raw4790step3Labels = labelEmbedding1 ∘ raw4790step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4790step3 raw4790step3Labels raw4790step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw4791 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4791step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4791step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4791step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4791step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4791 raw4791Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw4791 raw4791Labels = mixedMoment B raw4791step0 raw4791step0Labels := by
      have hz : ∀ j, raw4791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4791step0 = (fun i j => raw4791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4791step0 raw4791; decide +kernel
      have hl : raw4791step0Labels = raw4791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4791 raw4791Labels permutation346 hz
    mixedMoment B raw4791step0 raw4791step0Labels = mixedMoment B raw4791step1 raw4791step1Labels := by
      have ha : raw4791step1 = (fun i j => raw4791step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4791step1 raw4791step0; decide +kernel
      have hl : raw4791step1Labels = raw4791step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4791step0 raw4791step0Labels permutation137 permutation7
    mixedMoment B raw4791step1 raw4791step1Labels = mixedMoment B raw4791step2 raw4791step2Labels := by
      have ha : raw4791step2 = -raw4791step1 := by apply Matrix.ext; change ∀ i j, raw4791step2 i j = -(raw4791step1 i j); unfold raw4791step2 raw4791step1; decide +kernel
      have hl : raw4791step2Labels = raw4791step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4791step2 raw4791step2Labels = mixedMoment B raw4791step3 raw4791step3Labels := by
      have ha : raw4791step3 = raw4791step2 := by apply Matrix.ext; unfold raw4791step3 raw4791step2; decide +kernel
      have hl : raw4791step2Labels = labelEmbedding1 ∘ raw4791step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4791step2 raw4791step2Labels raw4791step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1700 node1700Labels := by rfl

def raw4792 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4792step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw4792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4792step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4792step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4792 raw4792Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw4792 raw4792Labels = mixedMoment B raw4792step0 raw4792step0Labels := by
      have hz : ∀ j, raw4792 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4792step0 = (fun i j => raw4792 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4792step0 raw4792; decide +kernel
      have hl : raw4792step0Labels = raw4792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4792 raw4792Labels permutation265 hz
    mixedMoment B raw4792step0 raw4792step0Labels = mixedMoment B raw4792step1 raw4792step1Labels := by
      have ha : raw4792step1 = (fun i j => raw4792step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4792step1 raw4792step0; decide +kernel
      have hl : raw4792step1Labels = raw4792step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4792step0 raw4792step0Labels permutation137 permutation7
    mixedMoment B raw4792step1 raw4792step1Labels = mixedMoment B raw4792step2 raw4792step2Labels := by
      have ha : raw4792step2 = -raw4792step1 := by apply Matrix.ext; change ∀ i j, raw4792step2 i j = -(raw4792step1 i j); unfold raw4792step2 raw4792step1; decide +kernel
      have hl : raw4792step2Labels = raw4792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4792step2 raw4792step2Labels = mixedMoment B raw4792step3 raw4792step3Labels := by
      have ha : raw4792step3 = raw4792step2 := by apply Matrix.ext; unfold raw4792step3 raw4792step2; decide +kernel
      have hl : raw4792step2Labels = labelEmbedding1 ∘ raw4792step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4792step2 raw4792step2Labels raw4792step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2235 node2235Labels := by rfl

def raw4793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4793step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4793 raw4793Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw4793 raw4793Labels = mixedMoment B raw4793step0 raw4793step0Labels := by
      have ha : raw4793step0 = (fun i j => raw4793 (permutation609 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4793step0 raw4793; decide +kernel
      have hl : raw4793step0Labels = raw4793Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4793 raw4793Labels permutation609 permutation7
    mixedMoment B raw4793step0 raw4793step0Labels = mixedMoment B raw4793step1 raw4793step1Labels := by
      have ha : raw4793step1 = -raw4793step0 := by apply Matrix.ext; change ∀ i j, raw4793step1 i j = -(raw4793step0 i j); unfold raw4793step1 raw4793step0; decide +kernel
      have hl : raw4793step1Labels = raw4793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4793step1 raw4793step1Labels = mixedMoment B raw4793step2 raw4793step2Labels := by
      have ha : raw4793step2 = raw4793step1 := by apply Matrix.ext; unfold raw4793step2 raw4793step1; decide +kernel
      have hl : raw4793step1Labels = labelEmbedding1 ∘ raw4793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4793step1 raw4793step1Labels raw4793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2187 node2187Labels := by rfl

def raw4794 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4794step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4794step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4794step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4794step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4794step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4794step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4794step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4794 raw4794Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw4794 raw4794Labels = mixedMoment B raw4794step0 raw4794step0Labels := by
      have hz : ∀ j, raw4794 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4794step0 = (fun i j => raw4794 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4794step0 raw4794; decide +kernel
      have hl : raw4794step0Labels = raw4794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4794 raw4794Labels permutation520 hz
    mixedMoment B raw4794step0 raw4794step0Labels = mixedMoment B raw4794step1 raw4794step1Labels := by
      have hz : ∀ j, raw4794step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4794step1 = (fun i j => raw4794step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4794step1 raw4794step0; decide +kernel
      have hl : raw4794step1Labels = raw4794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4794step0 raw4794step0Labels permutation56 hz
    mixedMoment B raw4794step1 raw4794step1Labels = mixedMoment B raw4794step2 raw4794step2Labels := by
      have ha : raw4794step2 = (fun i j => raw4794step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4794step2 raw4794step1; decide +kernel
      have hl : raw4794step2Labels = raw4794step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4794step1 raw4794step1Labels permutation29 permutation7
    mixedMoment B raw4794step2 raw4794step2Labels = mixedMoment B raw4794step3 raw4794step3Labels := by
      have ha : raw4794step3 = -raw4794step2 := by apply Matrix.ext; change ∀ i j, raw4794step3 i j = -(raw4794step2 i j); unfold raw4794step3 raw4794step2; decide +kernel
      have hl : raw4794step3Labels = raw4794step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4794step3 raw4794step3Labels = mixedMoment B raw4794step4 raw4794step4Labels := by
      have ha : raw4794step4 = raw4794step3 := by apply Matrix.ext; unfold raw4794step4 raw4794step3; decide +kernel
      have hl : raw4794step3Labels = labelEmbedding1 ∘ raw4794step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4794step3 raw4794step3Labels raw4794step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw4795 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4795step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4795step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4795step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4795 raw4795Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw4795 raw4795Labels = mixedMoment B raw4795step0 raw4795step0Labels := by
      have hz : ∀ j, raw4795 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4795step0 = (fun i j => raw4795 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4795step0 raw4795; decide +kernel
      have hl : raw4795step0Labels = raw4795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4795 raw4795Labels permutation265 hz
    mixedMoment B raw4795step0 raw4795step0Labels = mixedMoment B raw4795step1 raw4795step1Labels := by
      have ha : raw4795step1 = (fun i j => raw4795step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4795step1 raw4795step0; decide +kernel
      have hl : raw4795step1Labels = raw4795step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4795step0 raw4795step0Labels permutation137 permutation7
    mixedMoment B raw4795step1 raw4795step1Labels = mixedMoment B raw4795step2 raw4795step2Labels := by
      have ha : raw4795step2 = -raw4795step1 := by apply Matrix.ext; change ∀ i j, raw4795step2 i j = -(raw4795step1 i j); unfold raw4795step2 raw4795step1; decide +kernel
      have hl : raw4795step2Labels = raw4795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4795step2 raw4795step2Labels = mixedMoment B raw4795step3 raw4795step3Labels := by
      have ha : raw4795step3 = raw4795step2 := by apply Matrix.ext; unfold raw4795step3 raw4795step2; decide +kernel
      have hl : raw4795step2Labels = labelEmbedding1 ∘ raw4795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4795step2 raw4795step2Labels raw4795step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1700 node1700Labels := by rfl

def raw4796 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4796step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4796step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4796step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw4796step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4796step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4796step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4796step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4796step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4796 raw4796Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw4796 raw4796Labels = mixedMoment B raw4796step0 raw4796step0Labels := by
      have hz : ∀ j, raw4796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4796step0 = (fun i j => raw4796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4796step0 raw4796; decide +kernel
      have hl : raw4796step0Labels = raw4796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4796 raw4796Labels permutation346 hz
    mixedMoment B raw4796step0 raw4796step0Labels = mixedMoment B raw4796step1 raw4796step1Labels := by
      have hz : ∀ j, raw4796step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4796step1 = (fun i j => raw4796step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4796step1 raw4796step0; decide +kernel
      have hl : raw4796step1Labels = raw4796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4796step0 raw4796step0Labels permutation56 hz
    mixedMoment B raw4796step1 raw4796step1Labels = mixedMoment B raw4796step2 raw4796step2Labels := by
      have ha : raw4796step2 = (fun i j => raw4796step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4796step2 raw4796step1; decide +kernel
      have hl : raw4796step2Labels = raw4796step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4796step1 raw4796step1Labels permutation31 permutation7
    mixedMoment B raw4796step2 raw4796step2Labels = mixedMoment B raw4796step3 raw4796step3Labels := by
      have ha : raw4796step3 = -raw4796step2 := by apply Matrix.ext; change ∀ i j, raw4796step3 i j = -(raw4796step2 i j); unfold raw4796step3 raw4796step2; decide +kernel
      have hl : raw4796step3Labels = raw4796step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4796step3 raw4796step3Labels = mixedMoment B raw4796step4 raw4796step4Labels := by
      have ha : raw4796step4 = raw4796step3 := by apply Matrix.ext; unfold raw4796step4 raw4796step3; decide +kernel
      have hl : raw4796step3Labels = labelEmbedding1 ∘ raw4796step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4796step3 raw4796step3Labels raw4796step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw4797 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4797step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4797step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4797 raw4797Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw4797 raw4797Labels = mixedMoment B raw4797step0 raw4797step0Labels := by
      have hz : ∀ j, raw4797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4797step0 = (fun i j => raw4797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4797step0 raw4797; decide +kernel
      have hl : raw4797step0Labels = raw4797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4797 raw4797Labels permutation346 hz
    mixedMoment B raw4797step0 raw4797step0Labels = mixedMoment B raw4797step1 raw4797step1Labels := by
      have ha : raw4797step1 = (fun i j => raw4797step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4797step1 raw4797step0; decide +kernel
      have hl : raw4797step1Labels = raw4797step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4797step0 raw4797step0Labels permutation139 permutation7
    mixedMoment B raw4797step1 raw4797step1Labels = mixedMoment B raw4797step2 raw4797step2Labels := by
      have ha : raw4797step2 = -raw4797step1 := by apply Matrix.ext; change ∀ i j, raw4797step2 i j = -(raw4797step1 i j); unfold raw4797step2 raw4797step1; decide +kernel
      have hl : raw4797step2Labels = raw4797step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4797step2 raw4797step2Labels = mixedMoment B raw4797step3 raw4797step3Labels := by
      have ha : raw4797step3 = raw4797step2 := by apply Matrix.ext; unfold raw4797step3 raw4797step2; decide +kernel
      have hl : raw4797step2Labels = labelEmbedding1 ∘ raw4797step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4797step2 raw4797step2Labels raw4797step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw4798 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4798step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4798step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4798step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4798step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4798 raw4798Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw4798 raw4798Labels = mixedMoment B raw4798step0 raw4798step0Labels := by
      have hz : ∀ j, raw4798 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4798step0 = (fun i j => raw4798 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4798step0 raw4798; decide +kernel
      have hl : raw4798step0Labels = raw4798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4798 raw4798Labels permutation265 hz
    mixedMoment B raw4798step0 raw4798step0Labels = mixedMoment B raw4798step1 raw4798step1Labels := by
      have ha : raw4798step1 = (fun i j => raw4798step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4798step1 raw4798step0; decide +kernel
      have hl : raw4798step1Labels = raw4798step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4798step0 raw4798step0Labels permutation139 permutation7
    mixedMoment B raw4798step1 raw4798step1Labels = mixedMoment B raw4798step2 raw4798step2Labels := by
      have ha : raw4798step2 = -raw4798step1 := by apply Matrix.ext; change ∀ i j, raw4798step2 i j = -(raw4798step1 i j); unfold raw4798step2 raw4798step1; decide +kernel
      have hl : raw4798step2Labels = raw4798step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4798step2 raw4798step2Labels = mixedMoment B raw4798step3 raw4798step3Labels := by
      have ha : raw4798step3 = raw4798step2 := by apply Matrix.ext; unfold raw4798step3 raw4798step2; decide +kernel
      have hl : raw4798step2Labels = labelEmbedding1 ∘ raw4798step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4798step2 raw4798step2Labels raw4798step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw4799 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4799step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4799step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw4799step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4799step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw4799step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4799step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4799step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4799step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4799step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4799 raw4799Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw4799 raw4799Labels = mixedMoment B raw4799step0 raw4799step0Labels := by
      have hz : ∀ j, raw4799 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4799step0 = (fun i j => raw4799 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4799step0 raw4799; decide +kernel
      have hl : raw4799step0Labels = raw4799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4799 raw4799Labels permutation520 hz
    mixedMoment B raw4799step0 raw4799step0Labels = mixedMoment B raw4799step1 raw4799step1Labels := by
      have hz : ∀ j, raw4799step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4799step1 = (fun i j => raw4799step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4799step1 raw4799step0; decide +kernel
      have hl : raw4799step1Labels = raw4799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4799step0 raw4799step0Labels permutation80 hz
    mixedMoment B raw4799step1 raw4799step1Labels = mixedMoment B raw4799step2 raw4799step2Labels := by
      have hz : ∀ j, raw4799step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4799step2 = (fun i j => raw4799step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4799step2 raw4799step1; decide +kernel
      have hl : raw4799step2Labels = raw4799step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4799step1 raw4799step1Labels permutation14 hz
    mixedMoment B raw4799step2 raw4799step2Labels = mixedMoment B raw4799step3 raw4799step3Labels := by
      have ha : raw4799step3 = (fun i j => raw4799step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4799step3 raw4799step2; decide +kernel
      have hl : raw4799step3Labels = raw4799step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4799step2 raw4799step2Labels permutation7 permutation7
    mixedMoment B raw4799step3 raw4799step3Labels = mixedMoment B raw4799step4 raw4799step4Labels := by
      have ha : raw4799step4 = -raw4799step3 := by apply Matrix.ext; change ∀ i j, raw4799step4 i j = -(raw4799step3 i j); unfold raw4799step4 raw4799step3; decide +kernel
      have hl : raw4799step4Labels = raw4799step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4799step4 raw4799step4Labels = mixedMoment B raw4799step5 raw4799step5Labels := by
      have ha : raw4799step5 = raw4799step4 := by apply Matrix.ext; unfold raw4799step5 raw4799step4; decide +kernel
      have hl : raw4799step4Labels = labelEmbedding1 ∘ raw4799step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4799step4 raw4799step4Labels raw4799step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw4800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4800step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4800step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4800step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4800step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4800step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4800step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4800step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4800 raw4800Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw4800 raw4800Labels = mixedMoment B raw4800step0 raw4800step0Labels := by
      have hz : ∀ j, raw4800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4800step0 = (fun i j => raw4800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4800step0 raw4800; decide +kernel
      have hl : raw4800step0Labels = raw4800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4800 raw4800Labels permutation346 hz
    mixedMoment B raw4800step0 raw4800step0Labels = mixedMoment B raw4800step1 raw4800step1Labels := by
      have hz : ∀ j, raw4800step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4800step1 = (fun i j => raw4800step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4800step1 raw4800step0; decide +kernel
      have hl : raw4800step1Labels = raw4800step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4800step0 raw4800step0Labels permutation56 hz
    mixedMoment B raw4800step1 raw4800step1Labels = mixedMoment B raw4800step2 raw4800step2Labels := by
      have ha : raw4800step2 = (fun i j => raw4800step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4800step2 raw4800step1; decide +kernel
      have hl : raw4800step2Labels = raw4800step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4800step1 raw4800step1Labels permutation31 permutation7
    mixedMoment B raw4800step2 raw4800step2Labels = mixedMoment B raw4800step3 raw4800step3Labels := by
      have ha : raw4800step3 = -raw4800step2 := by apply Matrix.ext; change ∀ i j, raw4800step3 i j = -(raw4800step2 i j); unfold raw4800step3 raw4800step2; decide +kernel
      have hl : raw4800step3Labels = raw4800step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4800step3 raw4800step3Labels = mixedMoment B raw4800step4 raw4800step4Labels := by
      have ha : raw4800step4 = raw4800step3 := by apply Matrix.ext; unfold raw4800step4 raw4800step3; decide +kernel
      have hl : raw4800step3Labels = labelEmbedding1 ∘ raw4800step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4800step3 raw4800step3Labels raw4800step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw4801 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4801step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4801step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw4801step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4801step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw4801step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4801step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4801step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4801step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4801step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4801 raw4801Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw4801 raw4801Labels = mixedMoment B raw4801step0 raw4801step0Labels := by
      have hz : ∀ j, raw4801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4801step0 = (fun i j => raw4801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4801step0 raw4801; decide +kernel
      have hl : raw4801step0Labels = raw4801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4801 raw4801Labels permutation434 hz
    mixedMoment B raw4801step0 raw4801step0Labels = mixedMoment B raw4801step1 raw4801step1Labels := by
      have hz : ∀ j, raw4801step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4801step1 = (fun i j => raw4801step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4801step1 raw4801step0; decide +kernel
      have hl : raw4801step1Labels = raw4801step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4801step0 raw4801step0Labels permutation80 hz
    mixedMoment B raw4801step1 raw4801step1Labels = mixedMoment B raw4801step2 raw4801step2Labels := by
      have hz : ∀ j, raw4801step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4801step2 = (fun i j => raw4801step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4801step2 raw4801step1; decide +kernel
      have hl : raw4801step2Labels = raw4801step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4801step1 raw4801step1Labels permutation14 hz
    mixedMoment B raw4801step2 raw4801step2Labels = mixedMoment B raw4801step3 raw4801step3Labels := by
      have ha : raw4801step3 = (fun i j => raw4801step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4801step3 raw4801step2; decide +kernel
      have hl : raw4801step3Labels = raw4801step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4801step2 raw4801step2Labels permutation7 permutation7
    mixedMoment B raw4801step3 raw4801step3Labels = mixedMoment B raw4801step4 raw4801step4Labels := by
      have ha : raw4801step4 = -raw4801step3 := by apply Matrix.ext; change ∀ i j, raw4801step4 i j = -(raw4801step3 i j); unfold raw4801step4 raw4801step3; decide +kernel
      have hl : raw4801step4Labels = raw4801step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4801step4 raw4801step4Labels = mixedMoment B raw4801step5 raw4801step5Labels := by
      have ha : raw4801step5 = raw4801step4 := by apply Matrix.ext; unfold raw4801step5 raw4801step4; decide +kernel
      have hl : raw4801step4Labels = labelEmbedding1 ∘ raw4801step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4801step4 raw4801step4Labels raw4801step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw4802 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4802step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4802step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw4802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4802step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4802step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4802step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4802step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4802 raw4802Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw4802 raw4802Labels = mixedMoment B raw4802step0 raw4802step0Labels := by
      have hz : ∀ j, raw4802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4802step0 = (fun i j => raw4802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4802step0 raw4802; decide +kernel
      have hl : raw4802step0Labels = raw4802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4802 raw4802Labels permutation346 hz
    mixedMoment B raw4802step0 raw4802step0Labels = mixedMoment B raw4802step1 raw4802step1Labels := by
      have hz : ∀ j, raw4802step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4802step1 = (fun i j => raw4802step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4802step1 raw4802step0; decide +kernel
      have hl : raw4802step1Labels = raw4802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4802step0 raw4802step0Labels permutation56 hz
    mixedMoment B raw4802step1 raw4802step1Labels = mixedMoment B raw4802step2 raw4802step2Labels := by
      have ha : raw4802step2 = (fun i j => raw4802step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4802step2 raw4802step1; decide +kernel
      have hl : raw4802step2Labels = raw4802step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4802step1 raw4802step1Labels permutation29 permutation7
    mixedMoment B raw4802step2 raw4802step2Labels = mixedMoment B raw4802step3 raw4802step3Labels := by
      have ha : raw4802step3 = -raw4802step2 := by apply Matrix.ext; change ∀ i j, raw4802step3 i j = -(raw4802step2 i j); unfold raw4802step3 raw4802step2; decide +kernel
      have hl : raw4802step3Labels = raw4802step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4802step3 raw4802step3Labels = mixedMoment B raw4802step4 raw4802step4Labels := by
      have ha : raw4802step4 = raw4802step3 := by apply Matrix.ext; unfold raw4802step4 raw4802step3; decide +kernel
      have hl : raw4802step3Labels = labelEmbedding1 ∘ raw4802step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4802step3 raw4802step3Labels raw4802step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw4803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4803step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4803step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4803step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4803 raw4803Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4803 raw4803Labels = mixedMoment B raw4803step0 raw4803step0Labels := by
      have hz : ∀ j, raw4803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4803step0 = (fun i j => raw4803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4803step0 raw4803; decide +kernel
      have hl : raw4803step0Labels = raw4803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4803 raw4803Labels permutation346 hz
    mixedMoment B raw4803step0 raw4803step0Labels = mixedMoment B raw4803step1 raw4803step1Labels := by
      have ha : raw4803step1 = (fun i j => raw4803step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4803step1 raw4803step0; decide +kernel
      have hl : raw4803step1Labels = raw4803step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4803step0 raw4803step0Labels permutation137 permutation7
    mixedMoment B raw4803step1 raw4803step1Labels = mixedMoment B raw4803step2 raw4803step2Labels := by
      have ha : raw4803step2 = -raw4803step1 := by apply Matrix.ext; change ∀ i j, raw4803step2 i j = -(raw4803step1 i j); unfold raw4803step2 raw4803step1; decide +kernel
      have hl : raw4803step2Labels = raw4803step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4803step2 raw4803step2Labels = mixedMoment B raw4803step3 raw4803step3Labels := by
      have ha : raw4803step3 = raw4803step2 := by apply Matrix.ext; unfold raw4803step3 raw4803step2; decide +kernel
      have hl : raw4803step2Labels = labelEmbedding1 ∘ raw4803step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4803step2 raw4803step2Labels raw4803step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw4804 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4804step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4804step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4804step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4804 raw4804Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4804 raw4804Labels = mixedMoment B raw4804step0 raw4804step0Labels := by
      have hz : ∀ j, raw4804 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4804step0 = (fun i j => raw4804 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4804step0 raw4804; decide +kernel
      have hl : raw4804step0Labels = raw4804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4804 raw4804Labels permutation265 hz
    mixedMoment B raw4804step0 raw4804step0Labels = mixedMoment B raw4804step1 raw4804step1Labels := by
      have ha : raw4804step1 = (fun i j => raw4804step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4804step1 raw4804step0; decide +kernel
      have hl : raw4804step1Labels = raw4804step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4804step0 raw4804step0Labels permutation137 permutation7
    mixedMoment B raw4804step1 raw4804step1Labels = mixedMoment B raw4804step2 raw4804step2Labels := by
      have ha : raw4804step2 = -raw4804step1 := by apply Matrix.ext; change ∀ i j, raw4804step2 i j = -(raw4804step1 i j); unfold raw4804step2 raw4804step1; decide +kernel
      have hl : raw4804step2Labels = raw4804step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4804step2 raw4804step2Labels = mixedMoment B raw4804step3 raw4804step3Labels := by
      have ha : raw4804step3 = raw4804step2 := by apply Matrix.ext; unfold raw4804step3 raw4804step2; decide +kernel
      have hl : raw4804step2Labels = labelEmbedding1 ∘ raw4804step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4804step2 raw4804step2Labels raw4804step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw4805 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4805step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4805step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4805step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4805step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw4805step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4805step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4805step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4805step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4805step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4805 raw4805Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw4805 raw4805Labels = mixedMoment B raw4805step0 raw4805step0Labels := by
      have hz : ∀ j, raw4805 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4805step0 = (fun i j => raw4805 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4805step0 raw4805; decide +kernel
      have hl : raw4805step0Labels = raw4805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4805 raw4805Labels permutation520 hz
    mixedMoment B raw4805step0 raw4805step0Labels = mixedMoment B raw4805step1 raw4805step1Labels := by
      have hz : ∀ j, raw4805step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4805step1 = (fun i j => raw4805step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4805step1 raw4805step0; decide +kernel
      have hl : raw4805step1Labels = raw4805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4805step0 raw4805step0Labels permutation80 hz
    mixedMoment B raw4805step1 raw4805step1Labels = mixedMoment B raw4805step2 raw4805step2Labels := by
      have hz : ∀ j, raw4805step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4805step2 = (fun i j => raw4805step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4805step2 raw4805step1; decide +kernel
      have hl : raw4805step2Labels = raw4805step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4805step1 raw4805step1Labels permutation14 hz
    mixedMoment B raw4805step2 raw4805step2Labels = mixedMoment B raw4805step3 raw4805step3Labels := by
      have ha : raw4805step3 = (fun i j => raw4805step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4805step3 raw4805step2; decide +kernel
      have hl : raw4805step3Labels = raw4805step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4805step2 raw4805step2Labels permutation7 permutation7
    mixedMoment B raw4805step3 raw4805step3Labels = mixedMoment B raw4805step4 raw4805step4Labels := by
      have ha : raw4805step4 = -raw4805step3 := by apply Matrix.ext; change ∀ i j, raw4805step4 i j = -(raw4805step3 i j); unfold raw4805step4 raw4805step3; decide +kernel
      have hl : raw4805step4Labels = raw4805step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4805step4 raw4805step4Labels = mixedMoment B raw4805step5 raw4805step5Labels := by
      have ha : raw4805step5 = raw4805step4 := by apply Matrix.ext; unfold raw4805step5 raw4805step4; decide +kernel
      have hl : raw4805step4Labels = labelEmbedding1 ∘ raw4805step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4805step4 raw4805step4Labels raw4805step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw4806 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4806 raw4806Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw4806 raw4806Labels = mixedMoment B raw4806step0 raw4806step0Labels := by
      have hz : ∀ j, raw4806 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4806step0 = (fun i j => raw4806 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4806step0 raw4806; decide +kernel
      have hl : raw4806step0Labels = raw4806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4806 raw4806Labels permutation265 hz
    mixedMoment B raw4806step0 raw4806step0Labels = mixedMoment B raw4806step1 raw4806step1Labels := by
      have ha : raw4806step1 = (fun i j => raw4806step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4806step1 raw4806step0; decide +kernel
      have hl : raw4806step1Labels = raw4806step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4806step0 raw4806step0Labels permutation137 permutation2
    _ = mixedMoment B node2052 node2052Labels := by rfl

def raw4807 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw4807step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4807 raw4807Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw4807 raw4807Labels = mixedMoment B raw4807step0 raw4807step0Labels := by
      have hz : ∀ j, raw4807 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4807step0 = (fun i j => raw4807 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4807step0 raw4807; decide +kernel
      have hl : raw4807step0Labels = raw4807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4807 raw4807Labels permutation520 hz
    mixedMoment B raw4807step0 raw4807step0Labels = mixedMoment B raw4807step1 raw4807step1Labels := by
      have hz : ∀ j, raw4807step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4807step1 = (fun i j => raw4807step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4807step1 raw4807step0; decide +kernel
      have hl : raw4807step1Labels = raw4807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4807step0 raw4807step0Labels permutation80 hz
    mixedMoment B raw4807step1 raw4807step1Labels = mixedMoment B raw4807step2 raw4807step2Labels := by
      have hz : ∀ j, raw4807step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4807step2 = (fun i j => raw4807step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4807step2 raw4807step1; decide +kernel
      have hl : raw4807step2Labels = raw4807step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4807step1 raw4807step1Labels permutation14 hz
    mixedMoment B raw4807step2 raw4807step2Labels = mixedMoment B raw4807step3 raw4807step3Labels := by
      have ha : raw4807step3 = (fun i j => raw4807step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4807step3 raw4807step2; decide +kernel
      have hl : raw4807step3Labels = raw4807step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4807step2 raw4807step2Labels permutation7 permutation2
    _ = mixedMoment B node2292 node2292Labels := by rfl

def raw4808 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4808 raw4808Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw4808 raw4808Labels = mixedMoment B raw4808step0 raw4808step0Labels := by
      have hz : ∀ j, raw4808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4808step0 = (fun i j => raw4808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4808step0 raw4808; decide +kernel
      have hl : raw4808step0Labels = raw4808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4808 raw4808Labels permutation346 hz
    mixedMoment B raw4808step0 raw4808step0Labels = mixedMoment B raw4808step1 raw4808step1Labels := by
      have hz : ∀ j, raw4808step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4808step1 = (fun i j => raw4808step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4808step1 raw4808step0; decide +kernel
      have hl : raw4808step1Labels = raw4808step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4808step0 raw4808step0Labels permutation56 hz
    mixedMoment B raw4808step1 raw4808step1Labels = mixedMoment B raw4808step2 raw4808step2Labels := by
      have ha : raw4808step2 = (fun i j => raw4808step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4808step2 raw4808step1; decide +kernel
      have hl : raw4808step2Labels = raw4808step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4808step1 raw4808step1Labels permutation29 permutation2
    _ = mixedMoment B node1080 node1080Labels := by rfl

def raw4809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw4809step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4809step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4809step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4809 raw4809Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw4809 raw4809Labels = mixedMoment B raw4809step0 raw4809step0Labels := by
      have hz : ∀ j, raw4809 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4809step0 = (fun i j => raw4809 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4809step0 raw4809; decide +kernel
      have hl : raw4809step0Labels = raw4809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4809 raw4809Labels permutation434 hz
    mixedMoment B raw4809step0 raw4809step0Labels = mixedMoment B raw4809step1 raw4809step1Labels := by
      have hz : ∀ j, raw4809step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4809step1 = (fun i j => raw4809step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4809step1 raw4809step0; decide +kernel
      have hl : raw4809step1Labels = raw4809step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4809step0 raw4809step0Labels permutation80 hz
    mixedMoment B raw4809step1 raw4809step1Labels = mixedMoment B raw4809step2 raw4809step2Labels := by
      have ha : raw4809step2 = (fun i j => raw4809step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4809step2 raw4809step1; decide +kernel
      have hl : raw4809step2Labels = raw4809step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4809step1 raw4809step1Labels permutation31 permutation2
    mixedMoment B raw4809step2 raw4809step2Labels = mixedMoment B raw4809step3 raw4809step3Labels := by
      have ha : raw4809step3 = -raw4809step2 := by apply Matrix.ext; change ∀ i j, raw4809step3 i j = -(raw4809step2 i j); unfold raw4809step3 raw4809step2; decide +kernel
      have hl : raw4809step3Labels = raw4809step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw4810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4810step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4810 raw4810Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw4810 raw4810Labels = mixedMoment B raw4810step0 raw4810step0Labels := by
      have hz : ∀ j, raw4810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4810step0 = (fun i j => raw4810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4810step0 raw4810; decide +kernel
      have hl : raw4810step0Labels = raw4810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4810 raw4810Labels permutation434 hz
    mixedMoment B raw4810step0 raw4810step0Labels = mixedMoment B raw4810step1 raw4810step1Labels := by
      have ha : raw4810step1 = (fun i j => raw4810step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4810step1 raw4810step0; decide +kernel
      have hl : raw4810step1Labels = raw4810step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4810step0 raw4810step0Labels permutation139 permutation2
    mixedMoment B raw4810step1 raw4810step1Labels = mixedMoment B raw4810step2 raw4810step2Labels := by
      have ha : raw4810step2 = -raw4810step1 := by apply Matrix.ext; change ∀ i j, raw4810step2 i j = -(raw4810step1 i j); unfold raw4810step2 raw4810step1; decide +kernel
      have hl : raw4810step2Labels = raw4810step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw4811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4811 raw4811Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw4811 raw4811Labels = mixedMoment B raw4811step0 raw4811step0Labels := by
      have hz : ∀ j, raw4811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4811step0 = (fun i j => raw4811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4811step0 raw4811; decide +kernel
      have hl : raw4811step0Labels = raw4811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4811 raw4811Labels permutation346 hz
    mixedMoment B raw4811step0 raw4811step0Labels = mixedMoment B raw4811step1 raw4811step1Labels := by
      have ha : raw4811step1 = (fun i j => raw4811step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4811step1 raw4811step0; decide +kernel
      have hl : raw4811step1Labels = raw4811step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4811step0 raw4811step0Labels permutation139 permutation2
    mixedMoment B raw4811step1 raw4811step1Labels = mixedMoment B raw4811step2 raw4811step2Labels := by
      have ha : raw4811step2 = -raw4811step1 := by apply Matrix.ext; change ∀ i j, raw4811step2 i j = -(raw4811step1 i j); unfold raw4811step2 raw4811step1; decide +kernel
      have hl : raw4811step2Labels = raw4811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw4812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw4812step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw4812step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4812 raw4812Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw4812 raw4812Labels = mixedMoment B raw4812step0 raw4812step0Labels := by
      have hz : ∀ j, raw4812 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4812step0 = (fun i j => raw4812 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4812step0 raw4812; decide +kernel
      have hl : raw4812step0Labels = raw4812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4812 raw4812Labels permutation434 hz
    mixedMoment B raw4812step0 raw4812step0Labels = mixedMoment B raw4812step1 raw4812step1Labels := by
      have hz : ∀ j, raw4812step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4812step1 = (fun i j => raw4812step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4812step1 raw4812step0; decide +kernel
      have hl : raw4812step1Labels = raw4812step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4812step0 raw4812step0Labels permutation80 hz
    mixedMoment B raw4812step1 raw4812step1Labels = mixedMoment B raw4812step2 raw4812step2Labels := by
      have ha : raw4812step2 = (fun i j => raw4812step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4812step2 raw4812step1; decide +kernel
      have hl : raw4812step2Labels = raw4812step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4812step1 raw4812step1Labels permutation29 permutation2
    mixedMoment B raw4812step2 raw4812step2Labels = mixedMoment B raw4812step3 raw4812step3Labels := by
      have ha : raw4812step3 = -raw4812step2 := by apply Matrix.ext; change ∀ i j, raw4812step3 i j = -(raw4812step2 i j); unfold raw4812step3 raw4812step2; decide +kernel
      have hl : raw4812step3Labels = raw4812step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw4813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw4813step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw4813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4813 raw4813Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw4813 raw4813Labels = mixedMoment B raw4813step0 raw4813step0Labels := by
      have hz : ∀ j, raw4813 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4813step0 = (fun i j => raw4813 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4813step0 raw4813; decide +kernel
      have hl : raw4813step0Labels = raw4813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4813 raw4813Labels permutation434 hz
    mixedMoment B raw4813step0 raw4813step0Labels = mixedMoment B raw4813step1 raw4813step1Labels := by
      have hz : ∀ j, raw4813step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4813step1 = (fun i j => raw4813step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4813step1 raw4813step0; decide +kernel
      have hl : raw4813step1Labels = raw4813step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4813step0 raw4813step0Labels permutation80 hz
    mixedMoment B raw4813step1 raw4813step1Labels = mixedMoment B raw4813step2 raw4813step2Labels := by
      have ha : raw4813step2 = (fun i j => raw4813step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4813step2 raw4813step1; decide +kernel
      have hl : raw4813step2Labels = raw4813step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4813step1 raw4813step1Labels permutation29 permutation7
    mixedMoment B raw4813step2 raw4813step2Labels = mixedMoment B raw4813step3 raw4813step3Labels := by
      have ha : raw4813step3 = raw4813step2 := by apply Matrix.ext; unfold raw4813step3 raw4813step2; decide +kernel
      have hl : raw4813step2Labels = labelEmbedding10 ∘ raw4813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4813step2 raw4813step2Labels raw4813step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw4814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4814step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4814step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4814 raw4814Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw4814 raw4814Labels = mixedMoment B raw4814step0 raw4814step0Labels := by
      have hz : ∀ j, raw4814 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4814step0 = (fun i j => raw4814 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4814step0 raw4814; decide +kernel
      have hl : raw4814step0Labels = raw4814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4814 raw4814Labels permutation434 hz
    mixedMoment B raw4814step0 raw4814step0Labels = mixedMoment B raw4814step1 raw4814step1Labels := by
      have hz : ∀ j, raw4814step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4814step1 = (fun i j => raw4814step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4814step1 raw4814step0; decide +kernel
      have hl : raw4814step1Labels = raw4814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4814step0 raw4814step0Labels permutation80 hz
    mixedMoment B raw4814step1 raw4814step1Labels = mixedMoment B raw4814step2 raw4814step2Labels := by
      have ha : raw4814step2 = (fun i j => raw4814step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4814step2 raw4814step1; decide +kernel
      have hl : raw4814step2Labels = raw4814step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4814step1 raw4814step1Labels permutation10 permutation2
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw4815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4815 raw4815Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw4815 raw4815Labels = mixedMoment B raw4815step0 raw4815step0Labels := by
      have hz : ∀ j, raw4815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4815step0 = (fun i j => raw4815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4815step0 raw4815; decide +kernel
      have hl : raw4815step0Labels = raw4815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4815 raw4815Labels permutation434 hz
    mixedMoment B raw4815step0 raw4815step0Labels = mixedMoment B raw4815step1 raw4815step1Labels := by
      have ha : raw4815step1 = (fun i j => raw4815step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4815step1 raw4815step0; decide +kernel
      have hl : raw4815step1Labels = raw4815step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4815step0 raw4815step0Labels permutation139 permutation2
    mixedMoment B raw4815step1 raw4815step1Labels = mixedMoment B raw4815step2 raw4815step2Labels := by
      have ha : raw4815step2 = -raw4815step1 := by apply Matrix.ext; change ∀ i j, raw4815step2 i j = -(raw4815step1 i j); unfold raw4815step2 raw4815step1; decide +kernel
      have hl : raw4815step2Labels = raw4815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw4816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4816step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4816step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4816 raw4816Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw4816 raw4816Labels = mixedMoment B raw4816step0 raw4816step0Labels := by
      have hz : ∀ j, raw4816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4816step0 = (fun i j => raw4816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4816step0 raw4816; decide +kernel
      have hl : raw4816step0Labels = raw4816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4816 raw4816Labels permutation346 hz
    mixedMoment B raw4816step0 raw4816step0Labels = mixedMoment B raw4816step1 raw4816step1Labels := by
      have ha : raw4816step1 = (fun i j => raw4816step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4816step1 raw4816step0; decide +kernel
      have hl : raw4816step1Labels = raw4816step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4816step0 raw4816step0Labels permutation139 permutation2
    mixedMoment B raw4816step1 raw4816step1Labels = mixedMoment B raw4816step2 raw4816step2Labels := by
      have ha : raw4816step2 = -raw4816step1 := by apply Matrix.ext; change ∀ i j, raw4816step2 i j = -(raw4816step1 i j); unfold raw4816step2 raw4816step1; decide +kernel
      have hl : raw4816step2Labels = raw4816step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw4817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4817step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4817 raw4817Labels = mixedMoment B node5107 node5107Labels := by
  calc
    mixedMoment B raw4817 raw4817Labels = mixedMoment B raw4817step0 raw4817step0Labels := by
      have hz : ∀ j, raw4817 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4817step0 = (fun i j => raw4817 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4817step0 raw4817; decide +kernel
      have hl : raw4817step0Labels = raw4817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4817 raw4817Labels permutation434 hz
    mixedMoment B raw4817step0 raw4817step0Labels = mixedMoment B raw4817step1 raw4817step1Labels := by
      have hz : ∀ j, raw4817step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4817step1 = (fun i j => raw4817step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4817step1 raw4817step0; decide +kernel
      have hl : raw4817step1Labels = raw4817step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4817step0 raw4817step0Labels permutation80 hz
    mixedMoment B raw4817step1 raw4817step1Labels = mixedMoment B raw4817step2 raw4817step2Labels := by
      have ha : raw4817step2 = (fun i j => raw4817step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4817step2 raw4817step1; decide +kernel
      have hl : raw4817step2Labels = raw4817step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4817step1 raw4817step1Labels permutation10 permutation2
    _ = mixedMoment B node5107 node5107Labels := by rfl

def raw4818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4818step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw4818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4818 raw4818Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw4818 raw4818Labels = mixedMoment B raw4818step0 raw4818step0Labels := by
      have hz : ∀ j, raw4818 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4818step0 = (fun i j => raw4818 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4818step0 raw4818; decide +kernel
      have hl : raw4818step0Labels = raw4818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4818 raw4818Labels permutation434 hz
    mixedMoment B raw4818step0 raw4818step0Labels = mixedMoment B raw4818step1 raw4818step1Labels := by
      have hz : ∀ j, raw4818step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4818step1 = (fun i j => raw4818step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4818step1 raw4818step0; decide +kernel
      have hl : raw4818step1Labels = raw4818step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4818step0 raw4818step0Labels permutation80 hz
    mixedMoment B raw4818step1 raw4818step1Labels = mixedMoment B raw4818step2 raw4818step2Labels := by
      have ha : raw4818step2 = (fun i j => raw4818step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4818step2 raw4818step1; decide +kernel
      have hl : raw4818step2Labels = raw4818step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4818step1 raw4818step1Labels permutation10 permutation2
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw4819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4819 raw4819Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw4819 raw4819Labels = mixedMoment B raw4819step0 raw4819step0Labels := by
      have hz : ∀ j, raw4819 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4819step0 = (fun i j => raw4819 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4819step0 raw4819; decide +kernel
      have hl : raw4819step0Labels = raw4819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4819 raw4819Labels permutation434 hz
    mixedMoment B raw4819step0 raw4819step0Labels = mixedMoment B raw4819step1 raw4819step1Labels := by
      have ha : raw4819step1 = (fun i j => raw4819step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4819step1 raw4819step0; decide +kernel
      have hl : raw4819step1Labels = raw4819step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4819step0 raw4819step0Labels permutation44 permutation2
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw4820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4820 raw4820Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw4820 raw4820Labels = mixedMoment B raw4820step0 raw4820step0Labels := by
      have hz : ∀ j, raw4820 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4820step0 = (fun i j => raw4820 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4820step0 raw4820; decide +kernel
      have hl : raw4820step0Labels = raw4820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4820 raw4820Labels permutation434 hz
    mixedMoment B raw4820step0 raw4820step0Labels = mixedMoment B raw4820step1 raw4820step1Labels := by
      have ha : raw4820step1 = (fun i j => raw4820step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4820step1 raw4820step0; decide +kernel
      have hl : raw4820step1Labels = raw4820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4820step0 raw4820step0Labels permutation145 permutation2
    mixedMoment B raw4820step1 raw4820step1Labels = mixedMoment B raw4820step2 raw4820step2Labels := by
      have ha : raw4820step2 = -raw4820step1 := by apply Matrix.ext; change ∀ i j, raw4820step2 i j = -(raw4820step1 i j); unfold raw4820step2 raw4820step1; decide +kernel
      have hl : raw4820step2Labels = raw4820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw4821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4821 raw4821Labels = mixedMoment B node5127 node5127Labels := by
  calc
    mixedMoment B raw4821 raw4821Labels = mixedMoment B raw4821step0 raw4821step0Labels := by
      have ha : raw4821step0 = (fun i j => raw4821 (permutation212 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4821step0 raw4821; decide +kernel
      have hl : raw4821step0Labels = raw4821Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4821 raw4821Labels permutation212 permutation2
    _ = mixedMoment B node5127 node5127Labels := by rfl

def raw4822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4822 raw4822Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw4822 raw4822Labels = mixedMoment B raw4822step0 raw4822step0Labels := by
      have hz : ∀ j, raw4822 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4822step0 = (fun i j => raw4822 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4822step0 raw4822; decide +kernel
      have hl : raw4822step0Labels = raw4822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4822 raw4822Labels permutation434 hz
    mixedMoment B raw4822step0 raw4822step0Labels = mixedMoment B raw4822step1 raw4822step1Labels := by
      have ha : raw4822step1 = (fun i j => raw4822step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4822step1 raw4822step0; decide +kernel
      have hl : raw4822step1Labels = raw4822step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4822step0 raw4822step0Labels permutation44 permutation2
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw4823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4823 raw4823Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw4823 raw4823Labels = mixedMoment B raw4823step0 raw4823step0Labels := by
      have hz : ∀ j, raw4823 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4823step0 = (fun i j => raw4823 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4823step0 raw4823; decide +kernel
      have hl : raw4823step0Labels = raw4823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4823 raw4823Labels permutation434 hz
    mixedMoment B raw4823step0 raw4823step0Labels = mixedMoment B raw4823step1 raw4823step1Labels := by
      have ha : raw4823step1 = (fun i j => raw4823step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4823step1 raw4823step0; decide +kernel
      have hl : raw4823step1Labels = raw4823step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4823step0 raw4823step0Labels permutation44 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw4824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4824 raw4824Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw4824 raw4824Labels = mixedMoment B raw4824step0 raw4824step0Labels := by
      have hz : ∀ j, raw4824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4824step0 = (fun i j => raw4824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4824step0 raw4824; decide +kernel
      have hl : raw4824step0Labels = raw4824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4824 raw4824Labels permutation346 hz
    mixedMoment B raw4824step0 raw4824step0Labels = mixedMoment B raw4824step1 raw4824step1Labels := by
      have ha : raw4824step1 = (fun i j => raw4824step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4824step1 raw4824step0; decide +kernel
      have hl : raw4824step1Labels = raw4824step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4824step0 raw4824step0Labels permutation44 permutation2
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw4825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4825 raw4825Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw4825 raw4825Labels = mixedMoment B raw4825step0 raw4825step0Labels := by
      have hz : ∀ j, raw4825 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4825step0 = (fun i j => raw4825 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4825step0 raw4825; decide +kernel
      have hl : raw4825step0Labels = raw4825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4825 raw4825Labels permutation346 hz
    mixedMoment B raw4825step0 raw4825step0Labels = mixedMoment B raw4825step1 raw4825step1Labels := by
      have ha : raw4825step1 = (fun i j => raw4825step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4825step1 raw4825step0; decide +kernel
      have hl : raw4825step1Labels = raw4825step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4825step0 raw4825step0Labels permutation145 permutation2
    mixedMoment B raw4825step1 raw4825step1Labels = mixedMoment B raw4825step2 raw4825step2Labels := by
      have ha : raw4825step2 = -raw4825step1 := by apply Matrix.ext; change ∀ i j, raw4825step2 i j = -(raw4825step1 i j); unfold raw4825step2 raw4825step1; decide +kernel
      have hl : raw4825step2Labels = raw4825step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw4826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4826 raw4826Labels = mixedMoment B node5127 node5127Labels := by
  calc
    mixedMoment B raw4826 raw4826Labels = mixedMoment B raw4826step0 raw4826step0Labels := by
      have ha : raw4826step0 = (fun i j => raw4826 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4826step0 raw4826; decide +kernel
      have hl : raw4826step0Labels = raw4826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4826 raw4826Labels permutation188 permutation2
    _ = mixedMoment B node5127 node5127Labels := by rfl

def raw4827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4827 raw4827Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw4827 raw4827Labels = mixedMoment B raw4827step0 raw4827step0Labels := by
      have hz : ∀ j, raw4827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4827step0 = (fun i j => raw4827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4827step0 raw4827; decide +kernel
      have hl : raw4827step0Labels = raw4827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4827 raw4827Labels permutation346 hz
    mixedMoment B raw4827step0 raw4827step0Labels = mixedMoment B raw4827step1 raw4827step1Labels := by
      have ha : raw4827step1 = (fun i j => raw4827step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4827step1 raw4827step0; decide +kernel
      have hl : raw4827step1Labels = raw4827step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4827step0 raw4827step0Labels permutation44 permutation2
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw4828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4828 raw4828Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw4828 raw4828Labels = mixedMoment B raw4828step0 raw4828step0Labels := by
      have hz : ∀ j, raw4828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4828step0 = (fun i j => raw4828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4828step0 raw4828; decide +kernel
      have hl : raw4828step0Labels = raw4828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4828 raw4828Labels permutation346 hz
    mixedMoment B raw4828step0 raw4828step0Labels = mixedMoment B raw4828step1 raw4828step1Labels := by
      have ha : raw4828step1 = (fun i j => raw4828step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4828step1 raw4828step0; decide +kernel
      have hl : raw4828step1Labels = raw4828step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4828step0 raw4828step0Labels permutation44 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw4829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4829step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4829step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4829 raw4829Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw4829 raw4829Labels = mixedMoment B raw4829step0 raw4829step0Labels := by
      have hz : ∀ j, raw4829 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4829step0 = (fun i j => raw4829 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4829step0 raw4829; decide +kernel
      have hl : raw4829step0Labels = raw4829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4829 raw4829Labels permutation434 hz
    mixedMoment B raw4829step0 raw4829step0Labels = mixedMoment B raw4829step1 raw4829step1Labels := by
      have hz : ∀ j, raw4829step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4829step1 = (fun i j => raw4829step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4829step1 raw4829step0; decide +kernel
      have hl : raw4829step1Labels = raw4829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4829step0 raw4829step0Labels permutation80 hz
    mixedMoment B raw4829step1 raw4829step1Labels = mixedMoment B raw4829step2 raw4829step2Labels := by
      have ha : raw4829step2 = (fun i j => raw4829step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4829step2 raw4829step1; decide +kernel
      have hl : raw4829step2Labels = raw4829step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4829step1 raw4829step1Labels permutation8 permutation3
    mixedMoment B raw4829step2 raw4829step2Labels = mixedMoment B raw4829step3 raw4829step3Labels := by
      have ha : raw4829step3 = raw4829step2 := by apply Matrix.ext; unfold raw4829step3 raw4829step2; decide +kernel
      have hl : raw4829step2Labels = labelEmbedding6 ∘ raw4829step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4829step2 raw4829step2Labels raw4829step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw4830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4830 raw4830Labels = mixedMoment B node5201 node5201Labels := by
  calc
    mixedMoment B raw4830 raw4830Labels = mixedMoment B raw4830step0 raw4830step0Labels := by
      have hz : ∀ j, raw4830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4830step0 = (fun i j => raw4830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4830step0 raw4830; decide +kernel
      have hl : raw4830step0Labels = raw4830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4830 raw4830Labels permutation434 hz
    mixedMoment B raw4830step0 raw4830step0Labels = mixedMoment B raw4830step1 raw4830step1Labels := by
      have hz : ∀ j, raw4830step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4830step1 = (fun i j => raw4830step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4830step1 raw4830step0; decide +kernel
      have hl : raw4830step1Labels = raw4830step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4830step0 raw4830step0Labels permutation80 hz
    _ = mixedMoment B node5201 node5201Labels := by rfl

def raw4831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4831 raw4831Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw4831 raw4831Labels = mixedMoment B raw4831step0 raw4831step0Labels := by
      have hz : ∀ j, raw4831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4831step0 = (fun i j => raw4831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4831step0 raw4831; decide +kernel
      have hl : raw4831step0Labels = raw4831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4831 raw4831Labels permutation434 hz
    mixedMoment B raw4831step0 raw4831step0Labels = mixedMoment B raw4831step1 raw4831step1Labels := by
      have ha : raw4831step1 = (fun i j => raw4831step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4831step1 raw4831step0; decide +kernel
      have hl : raw4831step1Labels = raw4831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4831step0 raw4831step0Labels permutation38 permutation2
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw4832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4832 raw4832Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw4832 raw4832Labels = mixedMoment B raw4832step0 raw4832step0Labels := by
      have hz : ∀ j, raw4832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4832step0 = (fun i j => raw4832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4832step0 raw4832; decide +kernel
      have hl : raw4832step0Labels = raw4832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4832 raw4832Labels permutation346 hz
    mixedMoment B raw4832step0 raw4832step0Labels = mixedMoment B raw4832step1 raw4832step1Labels := by
      have ha : raw4832step1 = (fun i j => raw4832step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4832step1 raw4832step0; decide +kernel
      have hl : raw4832step1Labels = raw4832step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4832step0 raw4832step0Labels permutation38 permutation2
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw4833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw4833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw4833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4833 raw4833Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw4833 raw4833Labels = mixedMoment B raw4833step0 raw4833step0Labels := by
      have hz : ∀ j, raw4833 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4833step0 = (fun i j => raw4833 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4833step0 raw4833; decide +kernel
      have hl : raw4833step0Labels = raw4833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4833 raw4833Labels permutation434 hz
    mixedMoment B raw4833step0 raw4833step0Labels = mixedMoment B raw4833step1 raw4833step1Labels := by
      have hz : ∀ j, raw4833step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4833step1 = (fun i j => raw4833step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4833step1 raw4833step0; decide +kernel
      have hl : raw4833step1Labels = raw4833step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4833step0 raw4833step0Labels permutation80 hz
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw4834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw4834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4834 raw4834Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw4834 raw4834Labels = mixedMoment B raw4834step0 raw4834step0Labels := by
      have hz : ∀ j, raw4834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4834step0 = (fun i j => raw4834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4834step0 raw4834; decide +kernel
      have hl : raw4834step0Labels = raw4834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4834 raw4834Labels permutation434 hz
    mixedMoment B raw4834step0 raw4834step0Labels = mixedMoment B raw4834step1 raw4834step1Labels := by
      have hz : ∀ j, raw4834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4834step1 = (fun i j => raw4834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4834step1 raw4834step0; decide +kernel
      have hl : raw4834step1Labels = raw4834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4834step0 raw4834step0Labels permutation80 hz
    mixedMoment B raw4834step1 raw4834step1Labels = mixedMoment B raw4834step2 raw4834step2Labels := by
      have ha : raw4834step2 = (fun i j => raw4834step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4834step2 raw4834step1; decide +kernel
      have hl : raw4834step2Labels = raw4834step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4834step1 raw4834step1Labels permutation10 permutation2
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw4835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4835step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4835step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4835step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4835step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4835step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4835 raw4835Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw4835 raw4835Labels = mixedMoment B raw4835step0 raw4835step0Labels := by
      have hz : ∀ j, raw4835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4835step0 = (fun i j => raw4835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4835step0 raw4835; decide +kernel
      have hl : raw4835step0Labels = raw4835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4835 raw4835Labels permutation434 hz
    mixedMoment B raw4835step0 raw4835step0Labels = mixedMoment B raw4835step1 raw4835step1Labels := by
      have hz : ∀ j, raw4835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4835step1 = (fun i j => raw4835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4835step1 raw4835step0; decide +kernel
      have hl : raw4835step1Labels = raw4835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4835step0 raw4835step0Labels permutation80 hz
    mixedMoment B raw4835step1 raw4835step1Labels = mixedMoment B raw4835step2 raw4835step2Labels := by
      have ha : raw4835step2 = (fun i j => raw4835step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4835step2 raw4835step1; decide +kernel
      have hl : raw4835step2Labels = raw4835step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4835step1 raw4835step1Labels permutation31 permutation3
    mixedMoment B raw4835step2 raw4835step2Labels = mixedMoment B raw4835step3 raw4835step3Labels := by
      have ha : raw4835step3 = -raw4835step2 := by apply Matrix.ext; change ∀ i j, raw4835step3 i j = -(raw4835step2 i j); unfold raw4835step3 raw4835step2; decide +kernel
      have hl : raw4835step3Labels = raw4835step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4835step3 raw4835step3Labels = mixedMoment B raw4835step4 raw4835step4Labels := by
      have ha : raw4835step4 = raw4835step3 := by apply Matrix.ext; unfold raw4835step4 raw4835step3; decide +kernel
      have hl : raw4835step3Labels = labelEmbedding6 ∘ raw4835step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4835step3 raw4835step3Labels raw4835step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw4836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4836step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4836 raw4836Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw4836 raw4836Labels = mixedMoment B raw4836step0 raw4836step0Labels := by
      have hz : ∀ j, raw4836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4836step0 = (fun i j => raw4836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4836step0 raw4836; decide +kernel
      have hl : raw4836step0Labels = raw4836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4836 raw4836Labels permutation434 hz
    mixedMoment B raw4836step0 raw4836step0Labels = mixedMoment B raw4836step1 raw4836step1Labels := by
      have ha : raw4836step1 = (fun i j => raw4836step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4836step1 raw4836step0; decide +kernel
      have hl : raw4836step1Labels = raw4836step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4836step0 raw4836step0Labels permutation139 permutation2
    mixedMoment B raw4836step1 raw4836step1Labels = mixedMoment B raw4836step2 raw4836step2Labels := by
      have ha : raw4836step2 = -raw4836step1 := by apply Matrix.ext; change ∀ i j, raw4836step2 i j = -(raw4836step1 i j); unfold raw4836step2 raw4836step1; decide +kernel
      have hl : raw4836step2Labels = raw4836step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw4837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4837step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4837 raw4837Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw4837 raw4837Labels = mixedMoment B raw4837step0 raw4837step0Labels := by
      have hz : ∀ j, raw4837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4837step0 = (fun i j => raw4837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4837step0 raw4837; decide +kernel
      have hl : raw4837step0Labels = raw4837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4837 raw4837Labels permutation346 hz
    mixedMoment B raw4837step0 raw4837step0Labels = mixedMoment B raw4837step1 raw4837step1Labels := by
      have ha : raw4837step1 = (fun i j => raw4837step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4837step1 raw4837step0; decide +kernel
      have hl : raw4837step1Labels = raw4837step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4837step0 raw4837step0Labels permutation139 permutation2
    mixedMoment B raw4837step1 raw4837step1Labels = mixedMoment B raw4837step2 raw4837step2Labels := by
      have ha : raw4837step2 = -raw4837step1 := by apply Matrix.ext; change ∀ i j, raw4837step2 i j = -(raw4837step1 i j); unfold raw4837step2 raw4837step1; decide +kernel
      have hl : raw4837step2Labels = raw4837step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw4838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -2, -2]]
def raw4838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![4, -2, -2]]
def raw4838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![4, -2, -2]]
def raw4838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4838step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4838step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4838 raw4838Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw4838 raw4838Labels = mixedMoment B raw4838step0 raw4838step0Labels := by
      have hz : ∀ j, raw4838 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4838step0 = (fun i j => raw4838 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4838step0 raw4838; decide +kernel
      have hl : raw4838step0Labels = raw4838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4838 raw4838Labels permutation434 hz
    mixedMoment B raw4838step0 raw4838step0Labels = mixedMoment B raw4838step1 raw4838step1Labels := by
      have hz : ∀ j, raw4838step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4838step1 = (fun i j => raw4838step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4838step1 raw4838step0; decide +kernel
      have hl : raw4838step1Labels = raw4838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4838step0 raw4838step0Labels permutation80 hz
    mixedMoment B raw4838step1 raw4838step1Labels = mixedMoment B raw4838step2 raw4838step2Labels := by
      have ha : raw4838step2 = (fun i j => raw4838step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4838step2 raw4838step1; decide +kernel
      have hl : raw4838step2Labels = raw4838step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4838step1 raw4838step1Labels permutation29 permutation2
    mixedMoment B raw4838step2 raw4838step2Labels = mixedMoment B raw4838step3 raw4838step3Labels := by
      have ha : raw4838step3 = -raw4838step2 := by apply Matrix.ext; change ∀ i j, raw4838step3 i j = -(raw4838step2 i j); unfold raw4838step3 raw4838step2; decide +kernel
      have hl : raw4838step3Labels = raw4838step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw4839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4839step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw4839step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4839step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw4839step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4839 raw4839Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw4839 raw4839Labels = mixedMoment B raw4839step0 raw4839step0Labels := by
      have hz : ∀ j, raw4839 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4839step0 = (fun i j => raw4839 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4839step0 raw4839; decide +kernel
      have hl : raw4839step0Labels = raw4839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4839 raw4839Labels permutation434 hz
    mixedMoment B raw4839step0 raw4839step0Labels = mixedMoment B raw4839step1 raw4839step1Labels := by
      have hz : ∀ j, raw4839step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4839step1 = (fun i j => raw4839step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4839step1 raw4839step0; decide +kernel
      have hl : raw4839step1Labels = raw4839step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4839step0 raw4839step0Labels permutation80 hz
    mixedMoment B raw4839step1 raw4839step1Labels = mixedMoment B raw4839step2 raw4839step2Labels := by
      have ha : raw4839step2 = (fun i j => raw4839step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4839step2 raw4839step1; decide +kernel
      have hl : raw4839step2Labels = raw4839step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4839step1 raw4839step1Labels permutation31 permutation3
    mixedMoment B raw4839step2 raw4839step2Labels = mixedMoment B raw4839step3 raw4839step3Labels := by
      have ha : raw4839step3 = -raw4839step2 := by apply Matrix.ext; change ∀ i j, raw4839step3 i j = -(raw4839step2 i j); unfold raw4839step3 raw4839step2; decide +kernel
      have hl : raw4839step3Labels = raw4839step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw4840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4840 raw4840Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw4840 raw4840Labels = mixedMoment B raw4840step0 raw4840step0Labels := by
      have hz : ∀ j, raw4840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4840step0 = (fun i j => raw4840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4840step0 raw4840; decide +kernel
      have hl : raw4840step0Labels = raw4840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4840 raw4840Labels permutation434 hz
    mixedMoment B raw4840step0 raw4840step0Labels = mixedMoment B raw4840step1 raw4840step1Labels := by
      have ha : raw4840step1 = (fun i j => raw4840step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4840step1 raw4840step0; decide +kernel
      have hl : raw4840step1Labels = raw4840step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4840step0 raw4840step0Labels permutation149 permutation3
    mixedMoment B raw4840step1 raw4840step1Labels = mixedMoment B raw4840step2 raw4840step2Labels := by
      have ha : raw4840step2 = -raw4840step1 := by apply Matrix.ext; change ∀ i j, raw4840step2 i j = -(raw4840step1 i j); unfold raw4840step2 raw4840step1; decide +kernel
      have hl : raw4840step2Labels = raw4840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw4841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4841 raw4841Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw4841 raw4841Labels = mixedMoment B raw4841step0 raw4841step0Labels := by
      have hz : ∀ j, raw4841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4841step0 = (fun i j => raw4841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4841step0 raw4841; decide +kernel
      have hl : raw4841step0Labels = raw4841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4841 raw4841Labels permutation346 hz
    mixedMoment B raw4841step0 raw4841step0Labels = mixedMoment B raw4841step1 raw4841step1Labels := by
      have ha : raw4841step1 = (fun i j => raw4841step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4841step1 raw4841step0; decide +kernel
      have hl : raw4841step1Labels = raw4841step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4841step0 raw4841step0Labels permutation149 permutation3
    mixedMoment B raw4841step1 raw4841step1Labels = mixedMoment B raw4841step2 raw4841step2Labels := by
      have ha : raw4841step2 = -raw4841step1 := by apply Matrix.ext; change ∀ i j, raw4841step2 i j = -(raw4841step1 i j); unfold raw4841step2 raw4841step1; decide +kernel
      have hl : raw4841step2Labels = raw4841step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw4842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4842step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw4842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4842step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw4842step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4842 raw4842Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw4842 raw4842Labels = mixedMoment B raw4842step0 raw4842step0Labels := by
      have hz : ∀ j, raw4842 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4842step0 = (fun i j => raw4842 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4842step0 raw4842; decide +kernel
      have hl : raw4842step0Labels = raw4842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4842 raw4842Labels permutation434 hz
    mixedMoment B raw4842step0 raw4842step0Labels = mixedMoment B raw4842step1 raw4842step1Labels := by
      have hz : ∀ j, raw4842step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4842step1 = (fun i j => raw4842step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4842step1 raw4842step0; decide +kernel
      have hl : raw4842step1Labels = raw4842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4842step0 raw4842step0Labels permutation80 hz
    mixedMoment B raw4842step1 raw4842step1Labels = mixedMoment B raw4842step2 raw4842step2Labels := by
      have ha : raw4842step2 = (fun i j => raw4842step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4842step2 raw4842step1; decide +kernel
      have hl : raw4842step2Labels = raw4842step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4842step1 raw4842step1Labels permutation29 permutation3
    mixedMoment B raw4842step2 raw4842step2Labels = mixedMoment B raw4842step3 raw4842step3Labels := by
      have ha : raw4842step3 = -raw4842step2 := by apply Matrix.ext; change ∀ i j, raw4842step3 i j = -(raw4842step2 i j); unfold raw4842step3 raw4842step2; decide +kernel
      have hl : raw4842step3Labels = raw4842step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw4843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4843step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4843step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw4843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4843 raw4843Labels = mixedMoment B node4037 node4037Labels := by
  calc
    mixedMoment B raw4843 raw4843Labels = mixedMoment B raw4843step0 raw4843step0Labels := by
      have hz : ∀ j, raw4843 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4843step0 = (fun i j => raw4843 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4843step0 raw4843; decide +kernel
      have hl : raw4843step0Labels = raw4843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4843 raw4843Labels permutation434 hz
    mixedMoment B raw4843step0 raw4843step0Labels = mixedMoment B raw4843step1 raw4843step1Labels := by
      have hz : ∀ j, raw4843step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4843step1 = (fun i j => raw4843step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4843step1 raw4843step0; decide +kernel
      have hl : raw4843step1Labels = raw4843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4843step0 raw4843step0Labels permutation80 hz
    mixedMoment B raw4843step1 raw4843step1Labels = mixedMoment B raw4843step2 raw4843step2Labels := by
      have ha : raw4843step2 = (fun i j => raw4843step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4843step2 raw4843step1; decide +kernel
      have hl : raw4843step2Labels = raw4843step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4843step1 raw4843step1Labels permutation29 permutation6
    _ = mixedMoment B node4037 node4037Labels := by rfl

def raw4844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4844step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4844 raw4844Labels = mixedMoment B node1269 node1269Labels := by
  calc
    mixedMoment B raw4844 raw4844Labels = mixedMoment B raw4844step0 raw4844step0Labels := by
      have hz : ∀ j, raw4844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4844step0 = (fun i j => raw4844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4844step0 raw4844; decide +kernel
      have hl : raw4844step0Labels = raw4844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4844 raw4844Labels permutation434 hz
    mixedMoment B raw4844step0 raw4844step0Labels = mixedMoment B raw4844step1 raw4844step1Labels := by
      have hz : ∀ j, raw4844step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4844step1 = (fun i j => raw4844step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4844step1 raw4844step0; decide +kernel
      have hl : raw4844step1Labels = raw4844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4844step0 raw4844step0Labels permutation80 hz
    mixedMoment B raw4844step1 raw4844step1Labels = mixedMoment B raw4844step2 raw4844step2Labels := by
      have ha : raw4844step2 = (fun i j => raw4844step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4844step2 raw4844step1; decide +kernel
      have hl : raw4844step2Labels = raw4844step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4844step1 raw4844step1Labels permutation10 permutation3
    _ = mixedMoment B node1269 node1269Labels := by rfl

def raw4845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4845 raw4845Labels = mixedMoment B node2939 node2939Labels := by
  calc
    mixedMoment B raw4845 raw4845Labels = mixedMoment B raw4845step0 raw4845step0Labels := by
      have hz : ∀ j, raw4845 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4845step0 = (fun i j => raw4845 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4845step0 raw4845; decide +kernel
      have hl : raw4845step0Labels = raw4845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4845 raw4845Labels permutation434 hz
    mixedMoment B raw4845step0 raw4845step0Labels = mixedMoment B raw4845step1 raw4845step1Labels := by
      have ha : raw4845step1 = (fun i j => raw4845step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4845step1 raw4845step0; decide +kernel
      have hl : raw4845step1Labels = raw4845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4845step0 raw4845step0Labels permutation40 permutation3
    _ = mixedMoment B node2939 node2939Labels := by rfl

def raw4846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4846step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4846 raw4846Labels = mixedMoment B node2939 node2939Labels := by
  calc
    mixedMoment B raw4846 raw4846Labels = mixedMoment B raw4846step0 raw4846step0Labels := by
      have hz : ∀ j, raw4846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4846step0 = (fun i j => raw4846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4846step0 raw4846; decide +kernel
      have hl : raw4846step0Labels = raw4846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4846 raw4846Labels permutation346 hz
    mixedMoment B raw4846step0 raw4846step0Labels = mixedMoment B raw4846step1 raw4846step1Labels := by
      have ha : raw4846step1 = (fun i j => raw4846step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4846step1 raw4846step0; decide +kernel
      have hl : raw4846step1Labels = raw4846step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4846step0 raw4846step0Labels permutation40 permutation3
    _ = mixedMoment B node2939 node2939Labels := by rfl

def raw4847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4847step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4847step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw4847step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4847 raw4847Labels = mixedMoment B node3002 node3002Labels := by
  calc
    mixedMoment B raw4847 raw4847Labels = mixedMoment B raw4847step0 raw4847step0Labels := by
      have hz : ∀ j, raw4847 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4847step0 = (fun i j => raw4847 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4847step0 raw4847; decide +kernel
      have hl : raw4847step0Labels = raw4847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4847 raw4847Labels permutation434 hz
    mixedMoment B raw4847step0 raw4847step0Labels = mixedMoment B raw4847step1 raw4847step1Labels := by
      have hz : ∀ j, raw4847step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4847step1 = (fun i j => raw4847step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4847step1 raw4847step0; decide +kernel
      have hl : raw4847step1Labels = raw4847step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4847step0 raw4847step0Labels permutation80 hz
    mixedMoment B raw4847step1 raw4847step1Labels = mixedMoment B raw4847step2 raw4847step2Labels := by
      have ha : raw4847step2 = (fun i j => raw4847step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4847step2 raw4847step1; decide +kernel
      have hl : raw4847step2Labels = raw4847step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4847step1 raw4847step1Labels permutation10 permutation3
    _ = mixedMoment B node3002 node3002Labels := by rfl

def raw4848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4848step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw4848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4848 raw4848Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw4848 raw4848Labels = mixedMoment B raw4848step0 raw4848step0Labels := by
      have hz : ∀ j, raw4848 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4848step0 = (fun i j => raw4848 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4848step0 raw4848; decide +kernel
      have hl : raw4848step0Labels = raw4848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4848 raw4848Labels permutation434 hz
    mixedMoment B raw4848step0 raw4848step0Labels = mixedMoment B raw4848step1 raw4848step1Labels := by
      have hz : ∀ j, raw4848step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4848step1 = (fun i j => raw4848step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4848step1 raw4848step0; decide +kernel
      have hl : raw4848step1Labels = raw4848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4848step0 raw4848step0Labels permutation80 hz
    mixedMoment B raw4848step1 raw4848step1Labels = mixedMoment B raw4848step2 raw4848step2Labels := by
      have ha : raw4848step2 = (fun i j => raw4848step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4848step2 raw4848step1; decide +kernel
      have hl : raw4848step2Labels = raw4848step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4848step1 raw4848step1Labels permutation10 permutation3
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw4849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4849step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4849 raw4849Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw4849 raw4849Labels = mixedMoment B raw4849step0 raw4849step0Labels := by
      have hz : ∀ j, raw4849 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4849step0 = (fun i j => raw4849 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4849step0 raw4849; decide +kernel
      have hl : raw4849step0Labels = raw4849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4849 raw4849Labels permutation434 hz
    mixedMoment B raw4849step0 raw4849step0Labels = mixedMoment B raw4849step1 raw4849step1Labels := by
      have ha : raw4849step1 = (fun i j => raw4849step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4849step1 raw4849step0; decide +kernel
      have hl : raw4849step1Labels = raw4849step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4849step0 raw4849step0Labels permutation34 permutation3
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw4850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4850 raw4850Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw4850 raw4850Labels = mixedMoment B raw4850step0 raw4850step0Labels := by
      have hz : ∀ j, raw4850 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4850step0 = (fun i j => raw4850 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4850step0 raw4850; decide +kernel
      have hl : raw4850step0Labels = raw4850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4850 raw4850Labels permutation434 hz
    mixedMoment B raw4850step0 raw4850step0Labels = mixedMoment B raw4850step1 raw4850step1Labels := by
      have ha : raw4850step1 = (fun i j => raw4850step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4850step1 raw4850step0; decide +kernel
      have hl : raw4850step1Labels = raw4850step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4850step0 raw4850step0Labels permutation34 permutation3
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw4851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4851 raw4851Labels = mixedMoment B node2914 node2914Labels := by
  calc
    mixedMoment B raw4851 raw4851Labels = mixedMoment B raw4851step0 raw4851step0Labels := by
      have ha : raw4851step0 = (fun i j => raw4851 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4851step0 raw4851; decide +kernel
      have hl : raw4851step0Labels = raw4851Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4851 raw4851Labels permutation202 permutation3
    _ = mixedMoment B node2914 node2914Labels := by rfl

def raw4852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4852step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4852 raw4852Labels = mixedMoment B node2939 node2939Labels := by
  calc
    mixedMoment B raw4852 raw4852Labels = mixedMoment B raw4852step0 raw4852step0Labels := by
      have hz : ∀ j, raw4852 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4852step0 = (fun i j => raw4852 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4852step0 raw4852; decide +kernel
      have hl : raw4852step0Labels = raw4852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4852 raw4852Labels permutation434 hz
    mixedMoment B raw4852step0 raw4852step0Labels = mixedMoment B raw4852step1 raw4852step1Labels := by
      have ha : raw4852step1 = (fun i j => raw4852step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4852step1 raw4852step0; decide +kernel
      have hl : raw4852step1Labels = raw4852step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4852step0 raw4852step0Labels permutation143 permutation3
    mixedMoment B raw4852step1 raw4852step1Labels = mixedMoment B raw4852step2 raw4852step2Labels := by
      have ha : raw4852step2 = -raw4852step1 := by apply Matrix.ext; change ∀ i j, raw4852step2 i j = -(raw4852step1 i j); unfold raw4852step2 raw4852step1; decide +kernel
      have hl : raw4852step2Labels = raw4852step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2939 node2939Labels := by rfl

def raw4853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4853step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4853 raw4853Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw4853 raw4853Labels = mixedMoment B raw4853step0 raw4853step0Labels := by
      have hz : ∀ j, raw4853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4853step0 = (fun i j => raw4853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4853step0 raw4853; decide +kernel
      have hl : raw4853step0Labels = raw4853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4853 raw4853Labels permutation434 hz
    mixedMoment B raw4853step0 raw4853step0Labels = mixedMoment B raw4853step1 raw4853step1Labels := by
      have ha : raw4853step1 = (fun i j => raw4853step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4853step1 raw4853step0; decide +kernel
      have hl : raw4853step1Labels = raw4853step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4853step0 raw4853step0Labels permutation34 permutation3
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw4854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4854step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4854 raw4854Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw4854 raw4854Labels = mixedMoment B raw4854step0 raw4854step0Labels := by
      have hz : ∀ j, raw4854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4854step0 = (fun i j => raw4854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4854step0 raw4854; decide +kernel
      have hl : raw4854step0Labels = raw4854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4854 raw4854Labels permutation346 hz
    mixedMoment B raw4854step0 raw4854step0Labels = mixedMoment B raw4854step1 raw4854step1Labels := by
      have ha : raw4854step1 = (fun i j => raw4854step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4854step1 raw4854step0; decide +kernel
      have hl : raw4854step1Labels = raw4854step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4854step0 raw4854step0Labels permutation34 permutation3
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw4855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4855step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4855 raw4855Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw4855 raw4855Labels = mixedMoment B raw4855step0 raw4855step0Labels := by
      have hz : ∀ j, raw4855 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4855step0 = (fun i j => raw4855 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4855step0 raw4855; decide +kernel
      have hl : raw4855step0Labels = raw4855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4855 raw4855Labels permutation346 hz
    mixedMoment B raw4855step0 raw4855step0Labels = mixedMoment B raw4855step1 raw4855step1Labels := by
      have ha : raw4855step1 = (fun i j => raw4855step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4855step1 raw4855step0; decide +kernel
      have hl : raw4855step1Labels = raw4855step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4855step0 raw4855step0Labels permutation34 permutation3
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw4856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4856 raw4856Labels = mixedMoment B node2914 node2914Labels := by
  calc
    mixedMoment B raw4856 raw4856Labels = mixedMoment B raw4856step0 raw4856step0Labels := by
      have ha : raw4856step0 = (fun i j => raw4856 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4856step0 raw4856; decide +kernel
      have hl : raw4856step0Labels = raw4856Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4856 raw4856Labels permutation178 permutation3
    _ = mixedMoment B node2914 node2914Labels := by rfl

def raw4857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4857step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4857 raw4857Labels = mixedMoment B node2939 node2939Labels := by
  calc
    mixedMoment B raw4857 raw4857Labels = mixedMoment B raw4857step0 raw4857step0Labels := by
      have hz : ∀ j, raw4857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4857step0 = (fun i j => raw4857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4857step0 raw4857; decide +kernel
      have hl : raw4857step0Labels = raw4857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4857 raw4857Labels permutation346 hz
    mixedMoment B raw4857step0 raw4857step0Labels = mixedMoment B raw4857step1 raw4857step1Labels := by
      have ha : raw4857step1 = (fun i j => raw4857step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4857step1 raw4857step0; decide +kernel
      have hl : raw4857step1Labels = raw4857step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4857step0 raw4857step0Labels permutation143 permutation3
    mixedMoment B raw4857step1 raw4857step1Labels = mixedMoment B raw4857step2 raw4857step2Labels := by
      have ha : raw4857step2 = -raw4857step1 := by apply Matrix.ext; change ∀ i j, raw4857step2 i j = -(raw4857step1 i j); unfold raw4857step2 raw4857step1; decide +kernel
      have hl : raw4857step2Labels = raw4857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2939 node2939Labels := by rfl

def raw4858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4858step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4858 raw4858Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw4858 raw4858Labels = mixedMoment B raw4858step0 raw4858step0Labels := by
      have hz : ∀ j, raw4858 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4858step0 = (fun i j => raw4858 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4858step0 raw4858; decide +kernel
      have hl : raw4858step0Labels = raw4858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4858 raw4858Labels permutation346 hz
    mixedMoment B raw4858step0 raw4858step0Labels = mixedMoment B raw4858step1 raw4858step1Labels := by
      have ha : raw4858step1 = (fun i j => raw4858step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4858step1 raw4858step0; decide +kernel
      have hl : raw4858step1Labels = raw4858step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4858step0 raw4858step0Labels permutation34 permutation3
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw4859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4859step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4859step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4859 raw4859Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw4859 raw4859Labels = mixedMoment B raw4859step0 raw4859step0Labels := by
      have hz : ∀ j, raw4859 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4859step0 = (fun i j => raw4859 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4859step0 raw4859; decide +kernel
      have hl : raw4859step0Labels = raw4859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4859 raw4859Labels permutation434 hz
    mixedMoment B raw4859step0 raw4859step0Labels = mixedMoment B raw4859step1 raw4859step1Labels := by
      have hz : ∀ j, raw4859step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4859step1 = (fun i j => raw4859step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4859step1 raw4859step0; decide +kernel
      have hl : raw4859step1Labels = raw4859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4859step0 raw4859step0Labels permutation80 hz
    mixedMoment B raw4859step1 raw4859step1Labels = mixedMoment B raw4859step2 raw4859step2Labels := by
      have ha : raw4859step2 = (fun i j => raw4859step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4859step2 raw4859step1; decide +kernel
      have hl : raw4859step2Labels = raw4859step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4859step1 raw4859step1Labels permutation8 permutation3
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw4860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4860step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4860step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw4860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4860 raw4860Labels = mixedMoment B node2886 node2886Labels := by
  calc
    mixedMoment B raw4860 raw4860Labels = mixedMoment B raw4860step0 raw4860step0Labels := by
      have hz : ∀ j, raw4860 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4860step0 = (fun i j => raw4860 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4860step0 raw4860; decide +kernel
      have hl : raw4860step0Labels = raw4860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4860 raw4860Labels permutation434 hz
    mixedMoment B raw4860step0 raw4860step0Labels = mixedMoment B raw4860step1 raw4860step1Labels := by
      have hz : ∀ j, raw4860step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4860step1 = (fun i j => raw4860step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4860step1 raw4860step0; decide +kernel
      have hl : raw4860step1Labels = raw4860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4860step0 raw4860step0Labels permutation80 hz
    mixedMoment B raw4860step1 raw4860step1Labels = mixedMoment B raw4860step2 raw4860step2Labels := by
      have ha : raw4860step2 = (fun i j => raw4860step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4860step2 raw4860step1; decide +kernel
      have hl : raw4860step2Labels = raw4860step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4860step1 raw4860step1Labels permutation8 permutation3
    _ = mixedMoment B node2886 node2886Labels := by rfl

def raw4861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4861step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4861step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4861 raw4861Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw4861 raw4861Labels = mixedMoment B raw4861step0 raw4861step0Labels := by
      have hz : ∀ j, raw4861 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4861step0 = (fun i j => raw4861 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4861step0 raw4861; decide +kernel
      have hl : raw4861step0Labels = raw4861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4861 raw4861Labels permutation434 hz
    mixedMoment B raw4861step0 raw4861step0Labels = mixedMoment B raw4861step1 raw4861step1Labels := by
      have ha : raw4861step1 = (fun i j => raw4861step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4861step1 raw4861step0; decide +kernel
      have hl : raw4861step1Labels = raw4861step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4861step0 raw4861step0Labels permutation149 permutation3
    mixedMoment B raw4861step1 raw4861step1Labels = mixedMoment B raw4861step2 raw4861step2Labels := by
      have ha : raw4861step2 = -raw4861step1 := by apply Matrix.ext; change ∀ i j, raw4861step2 i j = -(raw4861step1 i j); unfold raw4861step2 raw4861step1; decide +kernel
      have hl : raw4861step2Labels = raw4861step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw4862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4862step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4862 raw4862Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw4862 raw4862Labels = mixedMoment B raw4862step0 raw4862step0Labels := by
      have hz : ∀ j, raw4862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4862step0 = (fun i j => raw4862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4862step0 raw4862; decide +kernel
      have hl : raw4862step0Labels = raw4862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4862 raw4862Labels permutation346 hz
    mixedMoment B raw4862step0 raw4862step0Labels = mixedMoment B raw4862step1 raw4862step1Labels := by
      have ha : raw4862step1 = (fun i j => raw4862step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4862step1 raw4862step0; decide +kernel
      have hl : raw4862step1Labels = raw4862step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4862step0 raw4862step0Labels permutation149 permutation3
    mixedMoment B raw4862step1 raw4862step1Labels = mixedMoment B raw4862step2 raw4862step2Labels := by
      have ha : raw4862step2 = -raw4862step1 := by apply Matrix.ext; change ∀ i j, raw4862step2 i j = -(raw4862step1 i j); unfold raw4862step2 raw4862step1; decide +kernel
      have hl : raw4862step2Labels = raw4862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw4863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw4863Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw4863step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4863step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw4863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4863 raw4863Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw4863 raw4863Labels = mixedMoment B raw4863step0 raw4863step0Labels := by
      have hz : ∀ j, raw4863 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4863step0 = (fun i j => raw4863 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4863step0 raw4863; decide +kernel
      have hl : raw4863step0Labels = raw4863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4863 raw4863Labels permutation434 hz
    mixedMoment B raw4863step0 raw4863step0Labels = mixedMoment B raw4863step1 raw4863step1Labels := by
      have hz : ∀ j, raw4863step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4863step1 = (fun i j => raw4863step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4863step1 raw4863step0; decide +kernel
      have hl : raw4863step1Labels = raw4863step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4863step0 raw4863step0Labels permutation80 hz
    mixedMoment B raw4863step1 raw4863step1Labels = mixedMoment B raw4863step2 raw4863step2Labels := by
      have ha : raw4863step2 = (fun i j => raw4863step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4863step2 raw4863step1; decide +kernel
      have hl : raw4863step2Labels = raw4863step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4863step1 raw4863step1Labels permutation8 permutation3
    _ = mixedMoment B node3103 node3103Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
