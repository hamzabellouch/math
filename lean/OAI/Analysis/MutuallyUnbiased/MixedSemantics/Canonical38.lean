import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4864step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4864step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw4864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4864 raw4864Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw4864 raw4864Labels = mixedMoment B raw4864step0 raw4864step0Labels := by
      have hz : ∀ j, raw4864 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4864step0 = (fun i j => raw4864 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4864step0 raw4864; decide +kernel
      have hl : raw4864step0Labels = raw4864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4864 raw4864Labels permutation434 hz
    mixedMoment B raw4864step0 raw4864step0Labels = mixedMoment B raw4864step1 raw4864step1Labels := by
      have hz : ∀ j, raw4864step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4864step1 = (fun i j => raw4864step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4864step1 raw4864step0; decide +kernel
      have hl : raw4864step1Labels = raw4864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4864step0 raw4864step0Labels permutation80 hz
    mixedMoment B raw4864step1 raw4864step1Labels = mixedMoment B raw4864step2 raw4864step2Labels := by
      have ha : raw4864step2 = (fun i j => raw4864step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4864step2 raw4864step1; decide +kernel
      have hl : raw4864step2Labels = raw4864step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4864step1 raw4864step1Labels permutation8 permutation3
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw4865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4865step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4865step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4865step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4865step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4865 raw4865Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw4865 raw4865Labels = mixedMoment B raw4865step0 raw4865step0Labels := by
      have hz : ∀ j, raw4865 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4865step0 = (fun i j => raw4865 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4865step0 raw4865; decide +kernel
      have hl : raw4865step0Labels = raw4865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4865 raw4865Labels permutation434 hz
    mixedMoment B raw4865step0 raw4865step0Labels = mixedMoment B raw4865step1 raw4865step1Labels := by
      have hz : ∀ j, raw4865step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4865step1 = (fun i j => raw4865step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4865step1 raw4865step0; decide +kernel
      have hl : raw4865step1Labels = raw4865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4865step0 raw4865step0Labels permutation80 hz
    mixedMoment B raw4865step1 raw4865step1Labels = mixedMoment B raw4865step2 raw4865step2Labels := by
      have ha : raw4865step2 = (fun i j => raw4865step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4865step2 raw4865step1; decide +kernel
      have hl : raw4865step2Labels = raw4865step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4865step1 raw4865step1Labels permutation31 permutation3
    mixedMoment B raw4865step2 raw4865step2Labels = mixedMoment B raw4865step3 raw4865step3Labels := by
      have ha : raw4865step3 = -raw4865step2 := by apply Matrix.ext; change ∀ i j, raw4865step3 i j = -(raw4865step2 i j); unfold raw4865step3 raw4865step2; decide +kernel
      have hl : raw4865step3Labels = raw4865step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw4866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4866 raw4866Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw4866 raw4866Labels = mixedMoment B raw4866step0 raw4866step0Labels := by
      have hz : ∀ j, raw4866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4866step0 = (fun i j => raw4866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4866step0 raw4866; decide +kernel
      have hl : raw4866step0Labels = raw4866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4866 raw4866Labels permutation434 hz
    mixedMoment B raw4866step0 raw4866step0Labels = mixedMoment B raw4866step1 raw4866step1Labels := by
      have ha : raw4866step1 = (fun i j => raw4866step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4866step1 raw4866step0; decide +kernel
      have hl : raw4866step1Labels = raw4866step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4866step0 raw4866step0Labels permutation149 permutation3
    mixedMoment B raw4866step1 raw4866step1Labels = mixedMoment B raw4866step2 raw4866step2Labels := by
      have ha : raw4866step2 = -raw4866step1 := by apply Matrix.ext; change ∀ i j, raw4866step2 i j = -(raw4866step1 i j); unfold raw4866step2 raw4866step1; decide +kernel
      have hl : raw4866step2Labels = raw4866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw4867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4867step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4867 raw4867Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw4867 raw4867Labels = mixedMoment B raw4867step0 raw4867step0Labels := by
      have hz : ∀ j, raw4867 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4867step0 = (fun i j => raw4867 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4867step0 raw4867; decide +kernel
      have hl : raw4867step0Labels = raw4867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4867 raw4867Labels permutation346 hz
    mixedMoment B raw4867step0 raw4867step0Labels = mixedMoment B raw4867step1 raw4867step1Labels := by
      have ha : raw4867step1 = (fun i j => raw4867step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4867step1 raw4867step0; decide +kernel
      have hl : raw4867step1Labels = raw4867step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4867step0 raw4867step0Labels permutation149 permutation3
    mixedMoment B raw4867step1 raw4867step1Labels = mixedMoment B raw4867step2 raw4867step2Labels := by
      have ha : raw4867step2 = -raw4867step1 := by apply Matrix.ext; change ∀ i j, raw4867step2 i j = -(raw4867step1 i j); unfold raw4867step2 raw4867step1; decide +kernel
      have hl : raw4867step2Labels = raw4867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw4868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -2, -2]]
def raw4868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![4, -2, -2]]
def raw4868step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![4, -2, -2]]
def raw4868step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4868step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4868 raw4868Labels = mixedMoment B node1269 node1269Labels := by
  calc
    mixedMoment B raw4868 raw4868Labels = mixedMoment B raw4868step0 raw4868step0Labels := by
      have hz : ∀ j, raw4868 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4868step0 = (fun i j => raw4868 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4868step0 raw4868; decide +kernel
      have hl : raw4868step0Labels = raw4868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4868 raw4868Labels permutation434 hz
    mixedMoment B raw4868step0 raw4868step0Labels = mixedMoment B raw4868step1 raw4868step1Labels := by
      have hz : ∀ j, raw4868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4868step1 = (fun i j => raw4868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4868step1 raw4868step0; decide +kernel
      have hl : raw4868step1Labels = raw4868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4868step0 raw4868step0Labels permutation80 hz
    mixedMoment B raw4868step1 raw4868step1Labels = mixedMoment B raw4868step2 raw4868step2Labels := by
      have ha : raw4868step2 = (fun i j => raw4868step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4868step2 raw4868step1; decide +kernel
      have hl : raw4868step2Labels = raw4868step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4868step1 raw4868step1Labels permutation29 permutation3
    mixedMoment B raw4868step2 raw4868step2Labels = mixedMoment B raw4868step3 raw4868step3Labels := by
      have ha : raw4868step3 = -raw4868step2 := by apply Matrix.ext; change ∀ i j, raw4868step3 i j = -(raw4868step2 i j); unfold raw4868step3 raw4868step2; decide +kernel
      have hl : raw4868step3Labels = raw4868step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1269 node1269Labels := by rfl

def raw4869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4869Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4869step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4869step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4869step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4869step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4869step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4869 raw4869Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw4869 raw4869Labels = mixedMoment B raw4869step0 raw4869step0Labels := by
      have hz : ∀ j, raw4869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4869step0 = (fun i j => raw4869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4869step0 raw4869; decide +kernel
      have hl : raw4869step0Labels = raw4869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4869 raw4869Labels permutation434 hz
    mixedMoment B raw4869step0 raw4869step0Labels = mixedMoment B raw4869step1 raw4869step1Labels := by
      have hz : ∀ j, raw4869step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4869step1 = (fun i j => raw4869step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4869step1 raw4869step0; decide +kernel
      have hl : raw4869step1Labels = raw4869step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4869step0 raw4869step0Labels permutation80 hz
    mixedMoment B raw4869step1 raw4869step1Labels = mixedMoment B raw4869step2 raw4869step2Labels := by
      have ha : raw4869step2 = (fun i j => raw4869step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4869step2 raw4869step1; decide +kernel
      have hl : raw4869step2Labels = raw4869step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4869step1 raw4869step1Labels permutation29 permutation7
    mixedMoment B raw4869step2 raw4869step2Labels = mixedMoment B raw4869step3 raw4869step3Labels := by
      have ha : raw4869step3 = raw4869step2 := by apply Matrix.ext; unfold raw4869step3 raw4869step2; decide +kernel
      have hl : raw4869step2Labels = labelEmbedding1 ∘ raw4869step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4869step2 raw4869step2Labels raw4869step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw4870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4870Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4870step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4870step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4870step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4870 raw4870Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw4870 raw4870Labels = mixedMoment B raw4870step0 raw4870step0Labels := by
      have hz : ∀ j, raw4870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4870step0 = (fun i j => raw4870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4870step0 raw4870; decide +kernel
      have hl : raw4870step0Labels = raw4870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4870 raw4870Labels permutation434 hz
    mixedMoment B raw4870step0 raw4870step0Labels = mixedMoment B raw4870step1 raw4870step1Labels := by
      have ha : raw4870step1 = (fun i j => raw4870step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4870step1 raw4870step0; decide +kernel
      have hl : raw4870step1Labels = raw4870step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4870step0 raw4870step0Labels permutation137 permutation7
    mixedMoment B raw4870step1 raw4870step1Labels = mixedMoment B raw4870step2 raw4870step2Labels := by
      have ha : raw4870step2 = raw4870step1 := by apply Matrix.ext; unfold raw4870step2 raw4870step1; decide +kernel
      have hl : raw4870step1Labels = labelEmbedding1 ∘ raw4870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4870step1 raw4870step1Labels raw4870step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw4871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4871Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4871step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4871step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4871 raw4871Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw4871 raw4871Labels = mixedMoment B raw4871step0 raw4871step0Labels := by
      have hz : ∀ j, raw4871 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4871step0 = (fun i j => raw4871 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4871step0 raw4871; decide +kernel
      have hl : raw4871step0Labels = raw4871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4871 raw4871Labels permutation346 hz
    mixedMoment B raw4871step0 raw4871step0Labels = mixedMoment B raw4871step1 raw4871step1Labels := by
      have ha : raw4871step1 = (fun i j => raw4871step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4871step1 raw4871step0; decide +kernel
      have hl : raw4871step1Labels = raw4871step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4871step0 raw4871step0Labels permutation137 permutation7
    mixedMoment B raw4871step1 raw4871step1Labels = mixedMoment B raw4871step2 raw4871step2Labels := by
      have ha : raw4871step2 = raw4871step1 := by apply Matrix.ext; unfold raw4871step2 raw4871step1; decide +kernel
      have hl : raw4871step1Labels = labelEmbedding1 ∘ raw4871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4871step1 raw4871step1Labels raw4871step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw4872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4872Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4872step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4872step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4872step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw4872step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4872step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw4872step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4872 raw4872Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw4872 raw4872Labels = mixedMoment B raw4872step0 raw4872step0Labels := by
      have hz : ∀ j, raw4872 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4872step0 = (fun i j => raw4872 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4872step0 raw4872; decide +kernel
      have hl : raw4872step0Labels = raw4872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4872 raw4872Labels permutation434 hz
    mixedMoment B raw4872step0 raw4872step0Labels = mixedMoment B raw4872step1 raw4872step1Labels := by
      have hz : ∀ j, raw4872step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4872step1 = (fun i j => raw4872step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4872step1 raw4872step0; decide +kernel
      have hl : raw4872step1Labels = raw4872step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4872step0 raw4872step0Labels permutation80 hz
    mixedMoment B raw4872step1 raw4872step1Labels = mixedMoment B raw4872step2 raw4872step2Labels := by
      have ha : raw4872step2 = (fun i j => raw4872step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4872step2 raw4872step1; decide +kernel
      have hl : raw4872step2Labels = raw4872step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4872step1 raw4872step1Labels permutation29 permutation7
    mixedMoment B raw4872step2 raw4872step2Labels = mixedMoment B raw4872step3 raw4872step3Labels := by
      have ha : raw4872step3 = raw4872step2 := by apply Matrix.ext; unfold raw4872step3 raw4872step2; decide +kernel
      have hl : raw4872step2Labels = labelEmbedding1 ∘ raw4872step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4872step2 raw4872step2Labels raw4872step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw4873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4873step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4873step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw4873step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4873step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw4873step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4873 raw4873Labels = mixedMoment B node3860 node3860Labels := by
  calc
    mixedMoment B raw4873 raw4873Labels = mixedMoment B raw4873step0 raw4873step0Labels := by
      have hz : ∀ j, raw4873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4873step0 = (fun i j => raw4873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4873step0 raw4873; decide +kernel
      have hl : raw4873step0Labels = raw4873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4873 raw4873Labels permutation434 hz
    mixedMoment B raw4873step0 raw4873step0Labels = mixedMoment B raw4873step1 raw4873step1Labels := by
      have hz : ∀ j, raw4873step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4873step1 = (fun i j => raw4873step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4873step1 raw4873step0; decide +kernel
      have hl : raw4873step1Labels = raw4873step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4873step0 raw4873step0Labels permutation80 hz
    mixedMoment B raw4873step1 raw4873step1Labels = mixedMoment B raw4873step2 raw4873step2Labels := by
      have ha : raw4873step2 = (fun i j => raw4873step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4873step2 raw4873step1; decide +kernel
      have hl : raw4873step2Labels = raw4873step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4873step1 raw4873step1Labels permutation29 permutation7
    mixedMoment B raw4873step2 raw4873step2Labels = mixedMoment B raw4873step3 raw4873step3Labels := by
      have ha : raw4873step3 = raw4873step2 := by apply Matrix.ext; unfold raw4873step3 raw4873step2; decide +kernel
      have hl : raw4873step2Labels = labelEmbedding1 ∘ raw4873step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4873step2 raw4873step2Labels raw4873step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3860 node3860Labels := by rfl

def raw4874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4874step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4874step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw4874step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4874step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw4874step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4874step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw4874step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4874 raw4874Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw4874 raw4874Labels = mixedMoment B raw4874step0 raw4874step0Labels := by
      have hz : ∀ j, raw4874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4874step0 = (fun i j => raw4874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4874step0 raw4874; decide +kernel
      have hl : raw4874step0Labels = raw4874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4874 raw4874Labels permutation434 hz
    mixedMoment B raw4874step0 raw4874step0Labels = mixedMoment B raw4874step1 raw4874step1Labels := by
      have hz : ∀ j, raw4874step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4874step1 = (fun i j => raw4874step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4874step1 raw4874step0; decide +kernel
      have hl : raw4874step1Labels = raw4874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4874step0 raw4874step0Labels permutation80 hz
    mixedMoment B raw4874step1 raw4874step1Labels = mixedMoment B raw4874step2 raw4874step2Labels := by
      have ha : raw4874step2 = (fun i j => raw4874step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4874step2 raw4874step1; decide +kernel
      have hl : raw4874step2Labels = raw4874step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4874step1 raw4874step1Labels permutation10 permutation7
    mixedMoment B raw4874step2 raw4874step2Labels = mixedMoment B raw4874step3 raw4874step3Labels := by
      have ha : raw4874step3 = -raw4874step2 := by apply Matrix.ext; change ∀ i j, raw4874step3 i j = -(raw4874step2 i j); unfold raw4874step3 raw4874step2; decide +kernel
      have hl : raw4874step3Labels = raw4874step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4874step3 raw4874step3Labels = mixedMoment B raw4874step4 raw4874step4Labels := by
      have ha : raw4874step4 = raw4874step3 := by apply Matrix.ext; unfold raw4874step4 raw4874step3; decide +kernel
      have hl : raw4874step3Labels = labelEmbedding1 ∘ raw4874step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4874step3 raw4874step3Labels raw4874step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw4875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4875Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4875step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4875step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4875 raw4875Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw4875 raw4875Labels = mixedMoment B raw4875step0 raw4875step0Labels := by
      have hz : ∀ j, raw4875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4875step0 = (fun i j => raw4875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4875step0 raw4875; decide +kernel
      have hl : raw4875step0Labels = raw4875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4875 raw4875Labels permutation434 hz
    mixedMoment B raw4875step0 raw4875step0Labels = mixedMoment B raw4875step1 raw4875step1Labels := by
      have ha : raw4875step1 = (fun i j => raw4875step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4875step1 raw4875step0; decide +kernel
      have hl : raw4875step1Labels = raw4875step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4875step0 raw4875step0Labels permutation137 permutation7
    mixedMoment B raw4875step1 raw4875step1Labels = mixedMoment B raw4875step2 raw4875step2Labels := by
      have ha : raw4875step2 = raw4875step1 := by apply Matrix.ext; unfold raw4875step2 raw4875step1; decide +kernel
      have hl : raw4875step1Labels = labelEmbedding1 ∘ raw4875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4875step1 raw4875step1Labels raw4875step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw4876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4876Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4876step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4876step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4876step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4876 raw4876Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw4876 raw4876Labels = mixedMoment B raw4876step0 raw4876step0Labels := by
      have hz : ∀ j, raw4876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4876step0 = (fun i j => raw4876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4876step0 raw4876; decide +kernel
      have hl : raw4876step0Labels = raw4876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4876 raw4876Labels permutation346 hz
    mixedMoment B raw4876step0 raw4876step0Labels = mixedMoment B raw4876step1 raw4876step1Labels := by
      have ha : raw4876step1 = (fun i j => raw4876step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4876step1 raw4876step0; decide +kernel
      have hl : raw4876step1Labels = raw4876step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4876step0 raw4876step0Labels permutation137 permutation7
    mixedMoment B raw4876step1 raw4876step1Labels = mixedMoment B raw4876step2 raw4876step2Labels := by
      have ha : raw4876step2 = raw4876step1 := by apply Matrix.ext; unfold raw4876step2 raw4876step1; decide +kernel
      have hl : raw4876step1Labels = labelEmbedding1 ∘ raw4876step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4876step1 raw4876step1Labels raw4876step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw4877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4877Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4877step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4877step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw4877step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4877step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw4877step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4877 raw4877Labels = mixedMoment B node3484 node3484Labels := by
  calc
    mixedMoment B raw4877 raw4877Labels = mixedMoment B raw4877step0 raw4877step0Labels := by
      have hz : ∀ j, raw4877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4877step0 = (fun i j => raw4877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4877step0 raw4877; decide +kernel
      have hl : raw4877step0Labels = raw4877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4877 raw4877Labels permutation434 hz
    mixedMoment B raw4877step0 raw4877step0Labels = mixedMoment B raw4877step1 raw4877step1Labels := by
      have hz : ∀ j, raw4877step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4877step1 = (fun i j => raw4877step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4877step1 raw4877step0; decide +kernel
      have hl : raw4877step1Labels = raw4877step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4877step0 raw4877step0Labels permutation80 hz
    mixedMoment B raw4877step1 raw4877step1Labels = mixedMoment B raw4877step2 raw4877step2Labels := by
      have ha : raw4877step2 = (fun i j => raw4877step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4877step2 raw4877step1; decide +kernel
      have hl : raw4877step2Labels = raw4877step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4877step1 raw4877step1Labels permutation29 permutation7
    mixedMoment B raw4877step2 raw4877step2Labels = mixedMoment B raw4877step3 raw4877step3Labels := by
      have ha : raw4877step3 = raw4877step2 := by apply Matrix.ext; unfold raw4877step3 raw4877step2; decide +kernel
      have hl : raw4877step2Labels = labelEmbedding1 ∘ raw4877step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4877step2 raw4877step2Labels raw4877step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3484 node3484Labels := by rfl

def raw4878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4878Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4878step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4878step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw4878step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4878step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw4878step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4878step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw4878step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4878 raw4878Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw4878 raw4878Labels = mixedMoment B raw4878step0 raw4878step0Labels := by
      have hz : ∀ j, raw4878 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4878step0 = (fun i j => raw4878 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4878step0 raw4878; decide +kernel
      have hl : raw4878step0Labels = raw4878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4878 raw4878Labels permutation434 hz
    mixedMoment B raw4878step0 raw4878step0Labels = mixedMoment B raw4878step1 raw4878step1Labels := by
      have hz : ∀ j, raw4878step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4878step1 = (fun i j => raw4878step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4878step1 raw4878step0; decide +kernel
      have hl : raw4878step1Labels = raw4878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4878step0 raw4878step0Labels permutation80 hz
    mixedMoment B raw4878step1 raw4878step1Labels = mixedMoment B raw4878step2 raw4878step2Labels := by
      have ha : raw4878step2 = (fun i j => raw4878step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4878step2 raw4878step1; decide +kernel
      have hl : raw4878step2Labels = raw4878step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4878step1 raw4878step1Labels permutation10 permutation7
    mixedMoment B raw4878step2 raw4878step2Labels = mixedMoment B raw4878step3 raw4878step3Labels := by
      have ha : raw4878step3 = -raw4878step2 := by apply Matrix.ext; change ∀ i j, raw4878step3 i j = -(raw4878step2 i j); unfold raw4878step3 raw4878step2; decide +kernel
      have hl : raw4878step3Labels = raw4878step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4878step3 raw4878step3Labels = mixedMoment B raw4878step4 raw4878step4Labels := by
      have ha : raw4878step4 = raw4878step3 := by apply Matrix.ext; unfold raw4878step4 raw4878step3; decide +kernel
      have hl : raw4878step3Labels = labelEmbedding1 ∘ raw4878step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4878step3 raw4878step3Labels raw4878step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw4879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4879Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4879step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw4879step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4879step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4879step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4879step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4879 raw4879Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw4879 raw4879Labels = mixedMoment B raw4879step0 raw4879step0Labels := by
      have hz : ∀ j, raw4879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4879step0 = (fun i j => raw4879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4879step0 raw4879; decide +kernel
      have hl : raw4879step0Labels = raw4879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4879 raw4879Labels permutation434 hz
    mixedMoment B raw4879step0 raw4879step0Labels = mixedMoment B raw4879step1 raw4879step1Labels := by
      have ha : raw4879step1 = (fun i j => raw4879step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4879step1 raw4879step0; decide +kernel
      have hl : raw4879step1Labels = raw4879step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4879step0 raw4879step0Labels permutation46 permutation7
    mixedMoment B raw4879step1 raw4879step1Labels = mixedMoment B raw4879step2 raw4879step2Labels := by
      have ha : raw4879step2 = -raw4879step1 := by apply Matrix.ext; change ∀ i j, raw4879step2 i j = -(raw4879step1 i j); unfold raw4879step2 raw4879step1; decide +kernel
      have hl : raw4879step2Labels = raw4879step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4879step2 raw4879step2Labels = mixedMoment B raw4879step3 raw4879step3Labels := by
      have ha : raw4879step3 = raw4879step2 := by apply Matrix.ext; unfold raw4879step3 raw4879step2; decide +kernel
      have hl : raw4879step2Labels = labelEmbedding1 ∘ raw4879step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4879step2 raw4879step2Labels raw4879step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw4880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4880Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4880step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw4880step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4880step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4880step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4880step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4880 raw4880Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw4880 raw4880Labels = mixedMoment B raw4880step0 raw4880step0Labels := by
      have hz : ∀ j, raw4880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4880step0 = (fun i j => raw4880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4880step0 raw4880; decide +kernel
      have hl : raw4880step0Labels = raw4880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4880 raw4880Labels permutation434 hz
    mixedMoment B raw4880step0 raw4880step0Labels = mixedMoment B raw4880step1 raw4880step1Labels := by
      have ha : raw4880step1 = (fun i j => raw4880step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4880step1 raw4880step0; decide +kernel
      have hl : raw4880step1Labels = raw4880step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4880step0 raw4880step0Labels permutation46 permutation7
    mixedMoment B raw4880step1 raw4880step1Labels = mixedMoment B raw4880step2 raw4880step2Labels := by
      have ha : raw4880step2 = -raw4880step1 := by apply Matrix.ext; change ∀ i j, raw4880step2 i j = -(raw4880step1 i j); unfold raw4880step2 raw4880step1; decide +kernel
      have hl : raw4880step2Labels = raw4880step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4880step2 raw4880step2Labels = mixedMoment B raw4880step3 raw4880step3Labels := by
      have ha : raw4880step3 = raw4880step2 := by apply Matrix.ext; unfold raw4880step3 raw4880step2; decide +kernel
      have hl : raw4880step2Labels = labelEmbedding1 ∘ raw4880step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4880step2 raw4880step2Labels raw4880step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw4881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4881Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4881step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4881 raw4881Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw4881 raw4881Labels = mixedMoment B raw4881step0 raw4881step0Labels := by
      have ha : raw4881step0 = (fun i j => raw4881 (permutation609 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4881step0 raw4881; decide +kernel
      have hl : raw4881step0Labels = raw4881Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4881 raw4881Labels permutation609 permutation7
    mixedMoment B raw4881step0 raw4881step0Labels = mixedMoment B raw4881step1 raw4881step1Labels := by
      have ha : raw4881step1 = raw4881step0 := by apply Matrix.ext; unfold raw4881step1 raw4881step0; decide +kernel
      have hl : raw4881step0Labels = labelEmbedding1 ∘ raw4881step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4881step0 raw4881step0Labels raw4881step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3513 node3513Labels := by rfl

def raw4882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4882Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4882step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw4882step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4882step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4882step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4882step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4882 raw4882Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw4882 raw4882Labels = mixedMoment B raw4882step0 raw4882step0Labels := by
      have hz : ∀ j, raw4882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4882step0 = (fun i j => raw4882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4882step0 raw4882; decide +kernel
      have hl : raw4882step0Labels = raw4882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4882 raw4882Labels permutation434 hz
    mixedMoment B raw4882step0 raw4882step0Labels = mixedMoment B raw4882step1 raw4882step1Labels := by
      have ha : raw4882step1 = (fun i j => raw4882step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4882step1 raw4882step0; decide +kernel
      have hl : raw4882step1Labels = raw4882step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4882step0 raw4882step0Labels permutation46 permutation7
    mixedMoment B raw4882step1 raw4882step1Labels = mixedMoment B raw4882step2 raw4882step2Labels := by
      have ha : raw4882step2 = -raw4882step1 := by apply Matrix.ext; change ∀ i j, raw4882step2 i j = -(raw4882step1 i j); unfold raw4882step2 raw4882step1; decide +kernel
      have hl : raw4882step2Labels = raw4882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4882step2 raw4882step2Labels = mixedMoment B raw4882step3 raw4882step3Labels := by
      have ha : raw4882step3 = raw4882step2 := by apply Matrix.ext; unfold raw4882step3 raw4882step2; decide +kernel
      have hl : raw4882step2Labels = labelEmbedding1 ∘ raw4882step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4882step2 raw4882step2Labels raw4882step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw4883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4883Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4883step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4883step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4883step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4883step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4883step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4883 raw4883Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw4883 raw4883Labels = mixedMoment B raw4883step0 raw4883step0Labels := by
      have hz : ∀ j, raw4883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4883step0 = (fun i j => raw4883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4883step0 raw4883; decide +kernel
      have hl : raw4883step0Labels = raw4883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4883 raw4883Labels permutation434 hz
    mixedMoment B raw4883step0 raw4883step0Labels = mixedMoment B raw4883step1 raw4883step1Labels := by
      have ha : raw4883step1 = (fun i j => raw4883step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4883step1 raw4883step0; decide +kernel
      have hl : raw4883step1Labels = raw4883step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4883step0 raw4883step0Labels permutation46 permutation7
    mixedMoment B raw4883step1 raw4883step1Labels = mixedMoment B raw4883step2 raw4883step2Labels := by
      have ha : raw4883step2 = -raw4883step1 := by apply Matrix.ext; change ∀ i j, raw4883step2 i j = -(raw4883step1 i j); unfold raw4883step2 raw4883step1; decide +kernel
      have hl : raw4883step2Labels = raw4883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4883step2 raw4883step2Labels = mixedMoment B raw4883step3 raw4883step3Labels := by
      have ha : raw4883step3 = raw4883step2 := by apply Matrix.ext; unfold raw4883step3 raw4883step2; decide +kernel
      have hl : raw4883step2Labels = labelEmbedding1 ∘ raw4883step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4883step2 raw4883step2Labels raw4883step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw4884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4884Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4884step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw4884step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4884step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4884step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4884step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4884 raw4884Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw4884 raw4884Labels = mixedMoment B raw4884step0 raw4884step0Labels := by
      have hz : ∀ j, raw4884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4884step0 = (fun i j => raw4884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4884step0 raw4884; decide +kernel
      have hl : raw4884step0Labels = raw4884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4884 raw4884Labels permutation346 hz
    mixedMoment B raw4884step0 raw4884step0Labels = mixedMoment B raw4884step1 raw4884step1Labels := by
      have ha : raw4884step1 = (fun i j => raw4884step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4884step1 raw4884step0; decide +kernel
      have hl : raw4884step1Labels = raw4884step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4884step0 raw4884step0Labels permutation46 permutation7
    mixedMoment B raw4884step1 raw4884step1Labels = mixedMoment B raw4884step2 raw4884step2Labels := by
      have ha : raw4884step2 = -raw4884step1 := by apply Matrix.ext; change ∀ i j, raw4884step2 i j = -(raw4884step1 i j); unfold raw4884step2 raw4884step1; decide +kernel
      have hl : raw4884step2Labels = raw4884step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4884step2 raw4884step2Labels = mixedMoment B raw4884step3 raw4884step3Labels := by
      have ha : raw4884step3 = raw4884step2 := by apply Matrix.ext; unfold raw4884step3 raw4884step2; decide +kernel
      have hl : raw4884step2Labels = labelEmbedding1 ∘ raw4884step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4884step2 raw4884step2Labels raw4884step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw4885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4885Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4885step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw4885step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4885step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4885step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4885step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4885 raw4885Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw4885 raw4885Labels = mixedMoment B raw4885step0 raw4885step0Labels := by
      have hz : ∀ j, raw4885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4885step0 = (fun i j => raw4885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4885step0 raw4885; decide +kernel
      have hl : raw4885step0Labels = raw4885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4885 raw4885Labels permutation346 hz
    mixedMoment B raw4885step0 raw4885step0Labels = mixedMoment B raw4885step1 raw4885step1Labels := by
      have ha : raw4885step1 = (fun i j => raw4885step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4885step1 raw4885step0; decide +kernel
      have hl : raw4885step1Labels = raw4885step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4885step0 raw4885step0Labels permutation46 permutation7
    mixedMoment B raw4885step1 raw4885step1Labels = mixedMoment B raw4885step2 raw4885step2Labels := by
      have ha : raw4885step2 = -raw4885step1 := by apply Matrix.ext; change ∀ i j, raw4885step2 i j = -(raw4885step1 i j); unfold raw4885step2 raw4885step1; decide +kernel
      have hl : raw4885step2Labels = raw4885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4885step2 raw4885step2Labels = mixedMoment B raw4885step3 raw4885step3Labels := by
      have ha : raw4885step3 = raw4885step2 := by apply Matrix.ext; unfold raw4885step3 raw4885step2; decide +kernel
      have hl : raw4885step2Labels = labelEmbedding1 ∘ raw4885step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4885step2 raw4885step2Labels raw4885step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw4886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4886Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4886step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4886 raw4886Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw4886 raw4886Labels = mixedMoment B raw4886step0 raw4886step0Labels := by
      have ha : raw4886step0 = (fun i j => raw4886 (permutation614 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4886step0 raw4886; decide +kernel
      have hl : raw4886step0Labels = raw4886Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4886 raw4886Labels permutation614 permutation7
    mixedMoment B raw4886step0 raw4886step0Labels = mixedMoment B raw4886step1 raw4886step1Labels := by
      have ha : raw4886step1 = raw4886step0 := by apply Matrix.ext; unfold raw4886step1 raw4886step0; decide +kernel
      have hl : raw4886step0Labels = labelEmbedding1 ∘ raw4886step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4886step0 raw4886step0Labels raw4886step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3513 node3513Labels := by rfl

def raw4887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4887Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4887step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw4887step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4887step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4887step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4887step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4887 raw4887Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw4887 raw4887Labels = mixedMoment B raw4887step0 raw4887step0Labels := by
      have hz : ∀ j, raw4887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4887step0 = (fun i j => raw4887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4887step0 raw4887; decide +kernel
      have hl : raw4887step0Labels = raw4887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4887 raw4887Labels permutation346 hz
    mixedMoment B raw4887step0 raw4887step0Labels = mixedMoment B raw4887step1 raw4887step1Labels := by
      have ha : raw4887step1 = (fun i j => raw4887step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4887step1 raw4887step0; decide +kernel
      have hl : raw4887step1Labels = raw4887step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4887step0 raw4887step0Labels permutation46 permutation7
    mixedMoment B raw4887step1 raw4887step1Labels = mixedMoment B raw4887step2 raw4887step2Labels := by
      have ha : raw4887step2 = -raw4887step1 := by apply Matrix.ext; change ∀ i j, raw4887step2 i j = -(raw4887step1 i j); unfold raw4887step2 raw4887step1; decide +kernel
      have hl : raw4887step2Labels = raw4887step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4887step2 raw4887step2Labels = mixedMoment B raw4887step3 raw4887step3Labels := by
      have ha : raw4887step3 = raw4887step2 := by apply Matrix.ext; unfold raw4887step3 raw4887step2; decide +kernel
      have hl : raw4887step2Labels = labelEmbedding1 ∘ raw4887step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4887step2 raw4887step2Labels raw4887step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw4888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4888Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4888step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4888step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4888step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4888step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4888step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4888 raw4888Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw4888 raw4888Labels = mixedMoment B raw4888step0 raw4888step0Labels := by
      have hz : ∀ j, raw4888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4888step0 = (fun i j => raw4888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4888step0 raw4888; decide +kernel
      have hl : raw4888step0Labels = raw4888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4888 raw4888Labels permutation346 hz
    mixedMoment B raw4888step0 raw4888step0Labels = mixedMoment B raw4888step1 raw4888step1Labels := by
      have ha : raw4888step1 = (fun i j => raw4888step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4888step1 raw4888step0; decide +kernel
      have hl : raw4888step1Labels = raw4888step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4888step0 raw4888step0Labels permutation46 permutation7
    mixedMoment B raw4888step1 raw4888step1Labels = mixedMoment B raw4888step2 raw4888step2Labels := by
      have ha : raw4888step2 = -raw4888step1 := by apply Matrix.ext; change ∀ i j, raw4888step2 i j = -(raw4888step1 i j); unfold raw4888step2 raw4888step1; decide +kernel
      have hl : raw4888step2Labels = raw4888step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4888step2 raw4888step2Labels = mixedMoment B raw4888step3 raw4888step3Labels := by
      have ha : raw4888step3 = raw4888step2 := by apply Matrix.ext; unfold raw4888step3 raw4888step2; decide +kernel
      have hl : raw4888step2Labels = labelEmbedding1 ∘ raw4888step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4888step2 raw4888step2Labels raw4888step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw4889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4889Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4889step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4889step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw4889step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4889step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4889step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4889step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4889step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4889 raw4889Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw4889 raw4889Labels = mixedMoment B raw4889step0 raw4889step0Labels := by
      have hz : ∀ j, raw4889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4889step0 = (fun i j => raw4889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4889step0 raw4889; decide +kernel
      have hl : raw4889step0Labels = raw4889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4889 raw4889Labels permutation434 hz
    mixedMoment B raw4889step0 raw4889step0Labels = mixedMoment B raw4889step1 raw4889step1Labels := by
      have hz : ∀ j, raw4889step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4889step1 = (fun i j => raw4889step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4889step1 raw4889step0; decide +kernel
      have hl : raw4889step1Labels = raw4889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4889step0 raw4889step0Labels permutation80 hz
    mixedMoment B raw4889step1 raw4889step1Labels = mixedMoment B raw4889step2 raw4889step2Labels := by
      have ha : raw4889step2 = (fun i j => raw4889step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4889step2 raw4889step1; decide +kernel
      have hl : raw4889step2Labels = raw4889step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4889step1 raw4889step1Labels permutation9 permutation5
    mixedMoment B raw4889step2 raw4889step2Labels = mixedMoment B raw4889step3 raw4889step3Labels := by
      have ha : raw4889step3 = -raw4889step2 := by apply Matrix.ext; change ∀ i j, raw4889step3 i j = -(raw4889step2 i j); unfold raw4889step3 raw4889step2; decide +kernel
      have hl : raw4889step3Labels = raw4889step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4889step3 raw4889step3Labels = mixedMoment B raw4889step4 raw4889step4Labels := by
      have ha : raw4889step4 = raw4889step3 := by apply Matrix.ext; unfold raw4889step4 raw4889step3; decide +kernel
      have hl : raw4889step3Labels = labelEmbedding1 ∘ raw4889step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4889step3 raw4889step3Labels raw4889step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw4890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4890Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4890step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4890step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4890step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4890step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4890step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4890 raw4890Labels = mixedMoment B node3579 node3579Labels := by
  calc
    mixedMoment B raw4890 raw4890Labels = mixedMoment B raw4890step0 raw4890step0Labels := by
      have hz : ∀ j, raw4890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4890step0 = (fun i j => raw4890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4890step0 raw4890; decide +kernel
      have hl : raw4890step0Labels = raw4890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4890 raw4890Labels permutation434 hz
    mixedMoment B raw4890step0 raw4890step0Labels = mixedMoment B raw4890step1 raw4890step1Labels := by
      have hz : ∀ j, raw4890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4890step1 = (fun i j => raw4890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4890step1 raw4890step0; decide +kernel
      have hl : raw4890step1Labels = raw4890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4890step0 raw4890step0Labels permutation80 hz
    mixedMoment B raw4890step1 raw4890step1Labels = mixedMoment B raw4890step2 raw4890step2Labels := by
      have ha : raw4890step2 = (fun i j => raw4890step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4890step2 raw4890step1; decide +kernel
      have hl : raw4890step2Labels = raw4890step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4890step1 raw4890step1Labels permutation29 permutation7
    mixedMoment B raw4890step2 raw4890step2Labels = mixedMoment B raw4890step3 raw4890step3Labels := by
      have ha : raw4890step3 = raw4890step2 := by apply Matrix.ext; unfold raw4890step3 raw4890step2; decide +kernel
      have hl : raw4890step2Labels = labelEmbedding1 ∘ raw4890step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4890step2 raw4890step2Labels raw4890step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3579 node3579Labels := by rfl

def raw4891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4891step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4891step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4891step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4891 raw4891Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw4891 raw4891Labels = mixedMoment B raw4891step0 raw4891step0Labels := by
      have hz : ∀ j, raw4891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4891step0 = (fun i j => raw4891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4891step0 raw4891; decide +kernel
      have hl : raw4891step0Labels = raw4891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4891 raw4891Labels permutation434 hz
    mixedMoment B raw4891step0 raw4891step0Labels = mixedMoment B raw4891step1 raw4891step1Labels := by
      have ha : raw4891step1 = (fun i j => raw4891step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4891step1 raw4891step0; decide +kernel
      have hl : raw4891step1Labels = raw4891step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4891step0 raw4891step0Labels permutation137 permutation7
    mixedMoment B raw4891step1 raw4891step1Labels = mixedMoment B raw4891step2 raw4891step2Labels := by
      have ha : raw4891step2 = raw4891step1 := by apply Matrix.ext; unfold raw4891step2 raw4891step1; decide +kernel
      have hl : raw4891step1Labels = labelEmbedding1 ∘ raw4891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4891step1 raw4891step1Labels raw4891step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw4892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4892step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4892 raw4892Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw4892 raw4892Labels = mixedMoment B raw4892step0 raw4892step0Labels := by
      have hz : ∀ j, raw4892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4892step0 = (fun i j => raw4892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4892step0 raw4892; decide +kernel
      have hl : raw4892step0Labels = raw4892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4892 raw4892Labels permutation346 hz
    mixedMoment B raw4892step0 raw4892step0Labels = mixedMoment B raw4892step1 raw4892step1Labels := by
      have ha : raw4892step1 = (fun i j => raw4892step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4892step1 raw4892step0; decide +kernel
      have hl : raw4892step1Labels = raw4892step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4892step0 raw4892step0Labels permutation137 permutation7
    mixedMoment B raw4892step1 raw4892step1Labels = mixedMoment B raw4892step2 raw4892step2Labels := by
      have ha : raw4892step2 = raw4892step1 := by apply Matrix.ext; unfold raw4892step2 raw4892step1; decide +kernel
      have hl : raw4892step1Labels = labelEmbedding1 ∘ raw4892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4892step1 raw4892step1Labels raw4892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw4893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw4893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw4893step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4893step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4893step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4893step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4893step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4893step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4893step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4893 raw4893Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw4893 raw4893Labels = mixedMoment B raw4893step0 raw4893step0Labels := by
      have hz : ∀ j, raw4893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4893step0 = (fun i j => raw4893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4893step0 raw4893; decide +kernel
      have hl : raw4893step0Labels = raw4893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4893 raw4893Labels permutation434 hz
    mixedMoment B raw4893step0 raw4893step0Labels = mixedMoment B raw4893step1 raw4893step1Labels := by
      have hz : ∀ j, raw4893step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4893step1 = (fun i j => raw4893step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4893step1 raw4893step0; decide +kernel
      have hl : raw4893step1Labels = raw4893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4893step0 raw4893step0Labels permutation80 hz
    mixedMoment B raw4893step1 raw4893step1Labels = mixedMoment B raw4893step2 raw4893step2Labels := by
      have ha : raw4893step2 = (fun i j => raw4893step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4893step2 raw4893step1; decide +kernel
      have hl : raw4893step2Labels = raw4893step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4893step1 raw4893step1Labels permutation10 permutation7
    mixedMoment B raw4893step2 raw4893step2Labels = mixedMoment B raw4893step3 raw4893step3Labels := by
      have ha : raw4893step3 = -raw4893step2 := by apply Matrix.ext; change ∀ i j, raw4893step3 i j = -(raw4893step2 i j); unfold raw4893step3 raw4893step2; decide +kernel
      have hl : raw4893step3Labels = raw4893step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4893step3 raw4893step3Labels = mixedMoment B raw4893step4 raw4893step4Labels := by
      have ha : raw4893step4 = raw4893step3 := by apply Matrix.ext; unfold raw4893step4 raw4893step3; decide +kernel
      have hl : raw4893step3Labels = labelEmbedding1 ∘ raw4893step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4893step3 raw4893step3Labels raw4893step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw4894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4894step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4894step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw4894step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4894step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw4894step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4894 raw4894Labels = mixedMoment B node3298 node3298Labels := by
  calc
    mixedMoment B raw4894 raw4894Labels = mixedMoment B raw4894step0 raw4894step0Labels := by
      have hz : ∀ j, raw4894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4894step0 = (fun i j => raw4894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4894step0 raw4894; decide +kernel
      have hl : raw4894step0Labels = raw4894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4894 raw4894Labels permutation434 hz
    mixedMoment B raw4894step0 raw4894step0Labels = mixedMoment B raw4894step1 raw4894step1Labels := by
      have hz : ∀ j, raw4894step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4894step1 = (fun i j => raw4894step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4894step1 raw4894step0; decide +kernel
      have hl : raw4894step1Labels = raw4894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4894step0 raw4894step0Labels permutation80 hz
    mixedMoment B raw4894step1 raw4894step1Labels = mixedMoment B raw4894step2 raw4894step2Labels := by
      have ha : raw4894step2 = (fun i j => raw4894step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4894step2 raw4894step1; decide +kernel
      have hl : raw4894step2Labels = raw4894step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4894step1 raw4894step1Labels permutation31 permutation5
    mixedMoment B raw4894step2 raw4894step2Labels = mixedMoment B raw4894step3 raw4894step3Labels := by
      have ha : raw4894step3 = raw4894step2 := by apply Matrix.ext; unfold raw4894step3 raw4894step2; decide +kernel
      have hl : raw4894step2Labels = labelEmbedding1 ∘ raw4894step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4894step2 raw4894step2Labels raw4894step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3298 node3298Labels := by rfl

def raw4895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4895step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4895step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4895step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4895step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4895step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4895 raw4895Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw4895 raw4895Labels = mixedMoment B raw4895step0 raw4895step0Labels := by
      have hz : ∀ j, raw4895 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4895step0 = (fun i j => raw4895 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4895step0 raw4895; decide +kernel
      have hl : raw4895step0Labels = raw4895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4895 raw4895Labels permutation434 hz
    mixedMoment B raw4895step0 raw4895step0Labels = mixedMoment B raw4895step1 raw4895step1Labels := by
      have hz : ∀ j, raw4895step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4895step1 = (fun i j => raw4895step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4895step1 raw4895step0; decide +kernel
      have hl : raw4895step1Labels = raw4895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4895step0 raw4895step0Labels permutation80 hz
    mixedMoment B raw4895step1 raw4895step1Labels = mixedMoment B raw4895step2 raw4895step2Labels := by
      have ha : raw4895step2 = (fun i j => raw4895step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4895step2 raw4895step1; decide +kernel
      have hl : raw4895step2Labels = raw4895step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4895step1 raw4895step1Labels permutation30 permutation5
    mixedMoment B raw4895step2 raw4895step2Labels = mixedMoment B raw4895step3 raw4895step3Labels := by
      have ha : raw4895step3 = raw4895step2 := by apply Matrix.ext; unfold raw4895step3 raw4895step2; decide +kernel
      have hl : raw4895step2Labels = labelEmbedding1 ∘ raw4895step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4895step2 raw4895step2Labels raw4895step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw4896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4896step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4896 raw4896Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw4896 raw4896Labels = mixedMoment B raw4896step0 raw4896step0Labels := by
      have hz : ∀ j, raw4896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4896step0 = (fun i j => raw4896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4896step0 raw4896; decide +kernel
      have hl : raw4896step0Labels = raw4896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4896 raw4896Labels permutation434 hz
    mixedMoment B raw4896step0 raw4896step0Labels = mixedMoment B raw4896step1 raw4896step1Labels := by
      have ha : raw4896step1 = (fun i j => raw4896step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4896step1 raw4896step0; decide +kernel
      have hl : raw4896step1Labels = raw4896step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4896step0 raw4896step0Labels permutation137 permutation7
    mixedMoment B raw4896step1 raw4896step1Labels = mixedMoment B raw4896step2 raw4896step2Labels := by
      have ha : raw4896step2 = raw4896step1 := by apply Matrix.ext; unfold raw4896step2 raw4896step1; decide +kernel
      have hl : raw4896step1Labels = labelEmbedding1 ∘ raw4896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4896step1 raw4896step1Labels raw4896step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw4897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4897step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4897step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4897step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4897 raw4897Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw4897 raw4897Labels = mixedMoment B raw4897step0 raw4897step0Labels := by
      have hz : ∀ j, raw4897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4897step0 = (fun i j => raw4897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4897step0 raw4897; decide +kernel
      have hl : raw4897step0Labels = raw4897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4897 raw4897Labels permutation346 hz
    mixedMoment B raw4897step0 raw4897step0Labels = mixedMoment B raw4897step1 raw4897step1Labels := by
      have ha : raw4897step1 = (fun i j => raw4897step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4897step1 raw4897step0; decide +kernel
      have hl : raw4897step1Labels = raw4897step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4897step0 raw4897step0Labels permutation137 permutation7
    mixedMoment B raw4897step1 raw4897step1Labels = mixedMoment B raw4897step2 raw4897step2Labels := by
      have ha : raw4897step2 = raw4897step1 := by apply Matrix.ext; unfold raw4897step2 raw4897step1; decide +kernel
      have hl : raw4897step1Labels = labelEmbedding1 ∘ raw4897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4897step1 raw4897step1Labels raw4897step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw4898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -2, -2]]
def raw4898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![4, -2, -2]]
def raw4898step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![4, -2, -2]]
def raw4898step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw4898step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4898step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw4898step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4898 raw4898Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw4898 raw4898Labels = mixedMoment B raw4898step0 raw4898step0Labels := by
      have hz : ∀ j, raw4898 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4898step0 = (fun i j => raw4898 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4898step0 raw4898; decide +kernel
      have hl : raw4898step0Labels = raw4898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4898 raw4898Labels permutation434 hz
    mixedMoment B raw4898step0 raw4898step0Labels = mixedMoment B raw4898step1 raw4898step1Labels := by
      have hz : ∀ j, raw4898step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4898step1 = (fun i j => raw4898step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4898step1 raw4898step0; decide +kernel
      have hl : raw4898step1Labels = raw4898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4898step0 raw4898step0Labels permutation80 hz
    mixedMoment B raw4898step1 raw4898step1Labels = mixedMoment B raw4898step2 raw4898step2Labels := by
      have ha : raw4898step2 = (fun i j => raw4898step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4898step2 raw4898step1; decide +kernel
      have hl : raw4898step2Labels = raw4898step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4898step1 raw4898step1Labels permutation29 permutation7
    mixedMoment B raw4898step2 raw4898step2Labels = mixedMoment B raw4898step3 raw4898step3Labels := by
      have ha : raw4898step3 = raw4898step2 := by apply Matrix.ext; unfold raw4898step3 raw4898step2; decide +kernel
      have hl : raw4898step2Labels = labelEmbedding1 ∘ raw4898step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4898step2 raw4898step2Labels raw4898step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw4899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4899 raw4899Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw4899 raw4899Labels = mixedMoment B raw4899step0 raw4899step0Labels := by
      have hz : ∀ j, raw4899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4899step0 = (fun i j => raw4899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4899step0 raw4899; decide +kernel
      have hl : raw4899step0Labels = raw4899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4899 raw4899Labels permutation434 hz
    mixedMoment B raw4899step0 raw4899step0Labels = mixedMoment B raw4899step1 raw4899step1Labels := by
      have hz : ∀ j, raw4899step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4899step1 = (fun i j => raw4899step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4899step1 raw4899step0; decide +kernel
      have hl : raw4899step1Labels = raw4899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4899step0 raw4899step0Labels permutation80 hz
    mixedMoment B raw4899step1 raw4899step1Labels = mixedMoment B raw4899step2 raw4899step2Labels := by
      have ha : raw4899step2 = (fun i j => raw4899step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4899step2 raw4899step1; decide +kernel
      have hl : raw4899step2Labels = raw4899step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4899step1 raw4899step1Labels permutation10 permutation2
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw4900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw4900step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4900step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4900step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4900 raw4900Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw4900 raw4900Labels = mixedMoment B raw4900step0 raw4900step0Labels := by
      have hz : ∀ j, raw4900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4900step0 = (fun i j => raw4900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4900step0 raw4900; decide +kernel
      have hl : raw4900step0Labels = raw4900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4900 raw4900Labels permutation434 hz
    mixedMoment B raw4900step0 raw4900step0Labels = mixedMoment B raw4900step1 raw4900step1Labels := by
      have hz : ∀ j, raw4900step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4900step1 = (fun i j => raw4900step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4900step1 raw4900step0; decide +kernel
      have hl : raw4900step1Labels = raw4900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4900step0 raw4900step0Labels permutation80 hz
    mixedMoment B raw4900step1 raw4900step1Labels = mixedMoment B raw4900step2 raw4900step2Labels := by
      have ha : raw4900step2 = (fun i j => raw4900step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4900step2 raw4900step1; decide +kernel
      have hl : raw4900step2Labels = raw4900step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4900step1 raw4900step1Labels permutation31 permutation2
    mixedMoment B raw4900step2 raw4900step2Labels = mixedMoment B raw4900step3 raw4900step3Labels := by
      have ha : raw4900step3 = -raw4900step2 := by apply Matrix.ext; change ∀ i j, raw4900step3 i j = -(raw4900step2 i j); unfold raw4900step3 raw4900step2; decide +kernel
      have hl : raw4900step3Labels = raw4900step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw4901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4901step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4901 raw4901Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw4901 raw4901Labels = mixedMoment B raw4901step0 raw4901step0Labels := by
      have hz : ∀ j, raw4901 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4901step0 = (fun i j => raw4901 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4901step0 raw4901; decide +kernel
      have hl : raw4901step0Labels = raw4901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4901 raw4901Labels permutation434 hz
    mixedMoment B raw4901step0 raw4901step0Labels = mixedMoment B raw4901step1 raw4901step1Labels := by
      have ha : raw4901step1 = (fun i j => raw4901step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4901step1 raw4901step0; decide +kernel
      have hl : raw4901step1Labels = raw4901step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4901step0 raw4901step0Labels permutation139 permutation2
    mixedMoment B raw4901step1 raw4901step1Labels = mixedMoment B raw4901step2 raw4901step2Labels := by
      have ha : raw4901step2 = -raw4901step1 := by apply Matrix.ext; change ∀ i j, raw4901step2 i j = -(raw4901step1 i j); unfold raw4901step2 raw4901step1; decide +kernel
      have hl : raw4901step2Labels = raw4901step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw4902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4902 raw4902Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw4902 raw4902Labels = mixedMoment B raw4902step0 raw4902step0Labels := by
      have hz : ∀ j, raw4902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4902step0 = (fun i j => raw4902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4902step0 raw4902; decide +kernel
      have hl : raw4902step0Labels = raw4902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4902 raw4902Labels permutation346 hz
    mixedMoment B raw4902step0 raw4902step0Labels = mixedMoment B raw4902step1 raw4902step1Labels := by
      have ha : raw4902step1 = (fun i j => raw4902step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4902step1 raw4902step0; decide +kernel
      have hl : raw4902step1Labels = raw4902step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4902step0 raw4902step0Labels permutation139 permutation2
    mixedMoment B raw4902step1 raw4902step1Labels = mixedMoment B raw4902step2 raw4902step2Labels := by
      have ha : raw4902step2 = -raw4902step1 := by apply Matrix.ext; change ∀ i j, raw4902step2 i j = -(raw4902step1 i j); unfold raw4902step2 raw4902step1; decide +kernel
      have hl : raw4902step2Labels = raw4902step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw4903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw4903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4903step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw4903step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4903 raw4903Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw4903 raw4903Labels = mixedMoment B raw4903step0 raw4903step0Labels := by
      have hz : ∀ j, raw4903 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4903step0 = (fun i j => raw4903 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4903step0 raw4903; decide +kernel
      have hl : raw4903step0Labels = raw4903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4903 raw4903Labels permutation434 hz
    mixedMoment B raw4903step0 raw4903step0Labels = mixedMoment B raw4903step1 raw4903step1Labels := by
      have hz : ∀ j, raw4903step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4903step1 = (fun i j => raw4903step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4903step1 raw4903step0; decide +kernel
      have hl : raw4903step1Labels = raw4903step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4903step0 raw4903step0Labels permutation80 hz
    mixedMoment B raw4903step1 raw4903step1Labels = mixedMoment B raw4903step2 raw4903step2Labels := by
      have ha : raw4903step2 = (fun i j => raw4903step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4903step2 raw4903step1; decide +kernel
      have hl : raw4903step2Labels = raw4903step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4903step1 raw4903step1Labels permutation29 permutation2
    mixedMoment B raw4903step2 raw4903step2Labels = mixedMoment B raw4903step3 raw4903step3Labels := by
      have ha : raw4903step3 = -raw4903step2 := by apply Matrix.ext; change ∀ i j, raw4903step3 i j = -(raw4903step2 i j); unfold raw4903step3 raw4903step2; decide +kernel
      have hl : raw4903step3Labels = raw4903step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw4904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw4904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4904 raw4904Labels = mixedMoment B node3905 node3905Labels := by
  calc
    mixedMoment B raw4904 raw4904Labels = mixedMoment B raw4904step0 raw4904step0Labels := by
      have hz : ∀ j, raw4904 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4904step0 = (fun i j => raw4904 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4904step0 raw4904; decide +kernel
      have hl : raw4904step0Labels = raw4904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4904 raw4904Labels permutation434 hz
    mixedMoment B raw4904step0 raw4904step0Labels = mixedMoment B raw4904step1 raw4904step1Labels := by
      have hz : ∀ j, raw4904step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4904step1 = (fun i j => raw4904step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4904step1 raw4904step0; decide +kernel
      have hl : raw4904step1Labels = raw4904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4904step0 raw4904step0Labels permutation80 hz
    mixedMoment B raw4904step1 raw4904step1Labels = mixedMoment B raw4904step2 raw4904step2Labels := by
      have ha : raw4904step2 = (fun i j => raw4904step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4904step2 raw4904step1; decide +kernel
      have hl : raw4904step2Labels = raw4904step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4904step1 raw4904step1Labels permutation10 permutation2
    _ = mixedMoment B node3905 node3905Labels := by rfl

def raw4905 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![2, -2]]
def raw4905Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4905step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]
def raw4905step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4905step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw4905step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4905step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw4905step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical4905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4905 raw4905Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw4905 raw4905Labels = mixedMoment B raw4905step0 raw4905step0Labels := by
      have hz : ∀ j, raw4905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4905step0 = (fun i j => raw4905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4905step0 raw4905; decide +kernel
      have hl : raw4905step0Labels = raw4905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4905 raw4905Labels permutation434 hz
    mixedMoment B raw4905step0 raw4905step0Labels = mixedMoment B raw4905step1 raw4905step1Labels := by
      have hz : ∀ j, raw4905step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4905step1 = (fun i j => raw4905step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4905step1 raw4905step0; decide +kernel
      have hl : raw4905step1Labels = raw4905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4905step0 raw4905step0Labels permutation80 hz
    mixedMoment B raw4905step1 raw4905step1Labels = mixedMoment B raw4905step2 raw4905step2Labels := by
      have ha : raw4905step2 = (fun i j => raw4905step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4905step2 raw4905step1; decide +kernel
      have hl : raw4905step2Labels = raw4905step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4905step1 raw4905step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw4906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4906 raw4906Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw4906 raw4906Labels = mixedMoment B raw4906step0 raw4906step0Labels := by
      have hz : ∀ j, raw4906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4906step0 = (fun i j => raw4906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4906step0 raw4906; decide +kernel
      have hl : raw4906step0Labels = raw4906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4906 raw4906Labels permutation434 hz
    mixedMoment B raw4906step0 raw4906step0Labels = mixedMoment B raw4906step1 raw4906step1Labels := by
      have hz : ∀ j, raw4906step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4906step1 = (fun i j => raw4906step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4906step1 raw4906step0; decide +kernel
      have hl : raw4906step1Labels = raw4906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4906step0 raw4906step0Labels permutation80 hz
    mixedMoment B raw4906step1 raw4906step1Labels = mixedMoment B raw4906step2 raw4906step2Labels := by
      have ha : raw4906step2 = (fun i j => raw4906step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4906step2 raw4906step1; decide +kernel
      have hl : raw4906step2Labels = raw4906step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4906step1 raw4906step1Labels permutation10 permutation2
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw4907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4907 raw4907Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw4907 raw4907Labels = mixedMoment B raw4907step0 raw4907step0Labels := by
      have hz : ∀ j, raw4907 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4907step0 = (fun i j => raw4907 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4907step0 raw4907; decide +kernel
      have hl : raw4907step0Labels = raw4907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4907 raw4907Labels permutation434 hz
    mixedMoment B raw4907step0 raw4907step0Labels = mixedMoment B raw4907step1 raw4907step1Labels := by
      have ha : raw4907step1 = (fun i j => raw4907step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4907step1 raw4907step0; decide +kernel
      have hl : raw4907step1Labels = raw4907step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4907step0 raw4907step0Labels permutation44 permutation2
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw4908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4908 raw4908Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw4908 raw4908Labels = mixedMoment B raw4908step0 raw4908step0Labels := by
      have hz : ∀ j, raw4908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4908step0 = (fun i j => raw4908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4908step0 raw4908; decide +kernel
      have hl : raw4908step0Labels = raw4908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4908 raw4908Labels permutation346 hz
    mixedMoment B raw4908step0 raw4908step0Labels = mixedMoment B raw4908step1 raw4908step1Labels := by
      have ha : raw4908step1 = (fun i j => raw4908step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4908step1 raw4908step0; decide +kernel
      have hl : raw4908step1Labels = raw4908step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4908step0 raw4908step0Labels permutation44 permutation2
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw4909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4909 raw4909Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw4909 raw4909Labels = mixedMoment B raw4909step0 raw4909step0Labels := by
      have hz : ∀ j, raw4909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4909step0 = (fun i j => raw4909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4909step0 raw4909; decide +kernel
      have hl : raw4909step0Labels = raw4909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4909 raw4909Labels permutation434 hz
    mixedMoment B raw4909step0 raw4909step0Labels = mixedMoment B raw4909step1 raw4909step1Labels := by
      have hz : ∀ j, raw4909step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4909step1 = (fun i j => raw4909step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4909step1 raw4909step0; decide +kernel
      have hl : raw4909step1Labels = raw4909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4909step0 raw4909step0Labels permutation80 hz
    _ = mixedMoment B node1264 node1264Labels := by rfl

def raw4910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw4910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4910 raw4910Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw4910 raw4910Labels = mixedMoment B raw4910step0 raw4910step0Labels := by
      have hz : ∀ j, raw4910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4910step0 = (fun i j => raw4910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4910step0 raw4910; decide +kernel
      have hl : raw4910step0Labels = raw4910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4910 raw4910Labels permutation434 hz
    mixedMoment B raw4910step0 raw4910step0Labels = mixedMoment B raw4910step1 raw4910step1Labels := by
      have hz : ∀ j, raw4910step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4910step1 = (fun i j => raw4910step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4910step1 raw4910step0; decide +kernel
      have hl : raw4910step1Labels = raw4910step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4910step0 raw4910step0Labels permutation80 hz
    mixedMoment B raw4910step1 raw4910step1Labels = mixedMoment B raw4910step2 raw4910step2Labels := by
      have ha : raw4910step2 = (fun i j => raw4910step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4910step2 raw4910step1; decide +kernel
      have hl : raw4910step2Labels = raw4910step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4910step1 raw4910step1Labels permutation10 permutation2
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw4911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4911 raw4911Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw4911 raw4911Labels = mixedMoment B raw4911step0 raw4911step0Labels := by
      have hz : ∀ j, raw4911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4911step0 = (fun i j => raw4911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4911step0 raw4911; decide +kernel
      have hl : raw4911step0Labels = raw4911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4911 raw4911Labels permutation434 hz
    mixedMoment B raw4911step0 raw4911step0Labels = mixedMoment B raw4911step1 raw4911step1Labels := by
      have ha : raw4911step1 = (fun i j => raw4911step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4911step1 raw4911step0; decide +kernel
      have hl : raw4911step1Labels = raw4911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4911step0 raw4911step0Labels permutation139 permutation2
    mixedMoment B raw4911step1 raw4911step1Labels = mixedMoment B raw4911step2 raw4911step2Labels := by
      have ha : raw4911step2 = -raw4911step1 := by apply Matrix.ext; change ∀ i j, raw4911step2 i j = -(raw4911step1 i j); unfold raw4911step2 raw4911step1; decide +kernel
      have hl : raw4911step2Labels = raw4911step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw4912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4912 raw4912Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw4912 raw4912Labels = mixedMoment B raw4912step0 raw4912step0Labels := by
      have hz : ∀ j, raw4912 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4912step0 = (fun i j => raw4912 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4912step0 raw4912; decide +kernel
      have hl : raw4912step0Labels = raw4912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4912 raw4912Labels permutation346 hz
    mixedMoment B raw4912step0 raw4912step0Labels = mixedMoment B raw4912step1 raw4912step1Labels := by
      have ha : raw4912step1 = (fun i j => raw4912step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4912step1 raw4912step0; decide +kernel
      have hl : raw4912step1Labels = raw4912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4912step0 raw4912step0Labels permutation139 permutation2
    mixedMoment B raw4912step1 raw4912step1Labels = mixedMoment B raw4912step2 raw4912step2Labels := by
      have ha : raw4912step2 = -raw4912step1 := by apply Matrix.ext; change ∀ i j, raw4912step2 i j = -(raw4912step1 i j); unfold raw4912step2 raw4912step1; decide +kernel
      have hl : raw4912step2Labels = raw4912step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw4913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4913 raw4913Labels = mixedMoment B node2517 node2517Labels := by
  calc
    mixedMoment B raw4913 raw4913Labels = mixedMoment B raw4913step0 raw4913step0Labels := by
      have hz : ∀ j, raw4913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4913step0 = (fun i j => raw4913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4913step0 raw4913; decide +kernel
      have hl : raw4913step0Labels = raw4913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4913 raw4913Labels permutation434 hz
    mixedMoment B raw4913step0 raw4913step0Labels = mixedMoment B raw4913step1 raw4913step1Labels := by
      have hz : ∀ j, raw4913step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4913step1 = (fun i j => raw4913step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4913step1 raw4913step0; decide +kernel
      have hl : raw4913step1Labels = raw4913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4913step0 raw4913step0Labels permutation80 hz
    mixedMoment B raw4913step1 raw4913step1Labels = mixedMoment B raw4913step2 raw4913step2Labels := by
      have ha : raw4913step2 = (fun i j => raw4913step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4913step2 raw4913step1; decide +kernel
      have hl : raw4913step2Labels = raw4913step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4913step1 raw4913step1Labels permutation10 permutation2
    _ = mixedMoment B node2517 node2517Labels := by rfl

def raw4914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw4914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4914 raw4914Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw4914 raw4914Labels = mixedMoment B raw4914step0 raw4914step0Labels := by
      have hz : ∀ j, raw4914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4914step0 = (fun i j => raw4914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4914step0 raw4914; decide +kernel
      have hl : raw4914step0Labels = raw4914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4914 raw4914Labels permutation434 hz
    mixedMoment B raw4914step0 raw4914step0Labels = mixedMoment B raw4914step1 raw4914step1Labels := by
      have hz : ∀ j, raw4914step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4914step1 = (fun i j => raw4914step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4914step1 raw4914step0; decide +kernel
      have hl : raw4914step1Labels = raw4914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4914step0 raw4914step0Labels permutation80 hz
    mixedMoment B raw4914step1 raw4914step1Labels = mixedMoment B raw4914step2 raw4914step2Labels := by
      have ha : raw4914step2 = (fun i j => raw4914step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4914step2 raw4914step1; decide +kernel
      have hl : raw4914step2Labels = raw4914step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4914step1 raw4914step1Labels permutation10 permutation2
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw4915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4915 raw4915Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw4915 raw4915Labels = mixedMoment B raw4915step0 raw4915step0Labels := by
      have hz : ∀ j, raw4915 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4915step0 = (fun i j => raw4915 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4915step0 raw4915; decide +kernel
      have hl : raw4915step0Labels = raw4915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4915 raw4915Labels permutation434 hz
    mixedMoment B raw4915step0 raw4915step0Labels = mixedMoment B raw4915step1 raw4915step1Labels := by
      have ha : raw4915step1 = (fun i j => raw4915step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4915step1 raw4915step0; decide +kernel
      have hl : raw4915step1Labels = raw4915step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4915step0 raw4915step0Labels permutation145 permutation2
    mixedMoment B raw4915step1 raw4915step1Labels = mixedMoment B raw4915step2 raw4915step2Labels := by
      have ha : raw4915step2 = -raw4915step1 := by apply Matrix.ext; change ∀ i j, raw4915step2 i j = -(raw4915step1 i j); unfold raw4915step2 raw4915step1; decide +kernel
      have hl : raw4915step2Labels = raw4915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2569 node2569Labels := by rfl

def raw4916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4916 raw4916Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw4916 raw4916Labels = mixedMoment B raw4916step0 raw4916step0Labels := by
      have hz : ∀ j, raw4916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4916step0 = (fun i j => raw4916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4916step0 raw4916; decide +kernel
      have hl : raw4916step0Labels = raw4916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4916 raw4916Labels permutation346 hz
    mixedMoment B raw4916step0 raw4916step0Labels = mixedMoment B raw4916step1 raw4916step1Labels := by
      have ha : raw4916step1 = (fun i j => raw4916step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4916step1 raw4916step0; decide +kernel
      have hl : raw4916step1Labels = raw4916step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4916step0 raw4916step0Labels permutation145 permutation2
    mixedMoment B raw4916step1 raw4916step1Labels = mixedMoment B raw4916step2 raw4916step2Labels := by
      have ha : raw4916step2 = -raw4916step1 := by apply Matrix.ext; change ∀ i j, raw4916step2 i j = -(raw4916step1 i j); unfold raw4916step2 raw4916step1; decide +kernel
      have hl : raw4916step2Labels = raw4916step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2569 node2569Labels := by rfl

def raw4917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4917 raw4917Labels = mixedMoment B node2635 node2635Labels := by
  calc
    mixedMoment B raw4917 raw4917Labels = mixedMoment B raw4917step0 raw4917step0Labels := by
      have hz : ∀ j, raw4917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4917step0 = (fun i j => raw4917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4917step0 raw4917; decide +kernel
      have hl : raw4917step0Labels = raw4917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4917 raw4917Labels permutation434 hz
    mixedMoment B raw4917step0 raw4917step0Labels = mixedMoment B raw4917step1 raw4917step1Labels := by
      have hz : ∀ j, raw4917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4917step1 = (fun i j => raw4917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4917step1 raw4917step0; decide +kernel
      have hl : raw4917step1Labels = raw4917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4917step0 raw4917step0Labels permutation80 hz
    _ = mixedMoment B node2635 node2635Labels := by rfl

def raw4918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4918step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4918step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4918step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4918 raw4918Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw4918 raw4918Labels = mixedMoment B raw4918step0 raw4918step0Labels := by
      have hz : ∀ j, raw4918 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4918step0 = (fun i j => raw4918 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4918step0 raw4918; decide +kernel
      have hl : raw4918step0Labels = raw4918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4918 raw4918Labels permutation434 hz
    mixedMoment B raw4918step0 raw4918step0Labels = mixedMoment B raw4918step1 raw4918step1Labels := by
      have hz : ∀ j, raw4918step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4918step1 = (fun i j => raw4918step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4918step1 raw4918step0; decide +kernel
      have hl : raw4918step1Labels = raw4918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4918step0 raw4918step0Labels permutation80 hz
    mixedMoment B raw4918step1 raw4918step1Labels = mixedMoment B raw4918step2 raw4918step2Labels := by
      have ha : raw4918step2 = (fun i j => raw4918step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4918step2 raw4918step1; decide +kernel
      have hl : raw4918step2Labels = raw4918step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4918step1 raw4918step1Labels permutation31 permutation2
    mixedMoment B raw4918step2 raw4918step2Labels = mixedMoment B raw4918step3 raw4918step3Labels := by
      have ha : raw4918step3 = -raw4918step2 := by apply Matrix.ext; change ∀ i j, raw4918step3 i j = -(raw4918step2 i j); unfold raw4918step3 raw4918step2; decide +kernel
      have hl : raw4918step3Labels = raw4918step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1264 node1264Labels := by rfl

def raw4919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4919 raw4919Labels = mixedMoment B node2542 node2542Labels := by
  calc
    mixedMoment B raw4919 raw4919Labels = mixedMoment B raw4919step0 raw4919step0Labels := by
      have ha : raw4919step0 = (fun i j => raw4919 (permutation212 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4919step0 raw4919; decide +kernel
      have hl : raw4919step0Labels = raw4919Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4919 raw4919Labels permutation212 permutation2
    _ = mixedMoment B node2542 node2542Labels := by rfl

def raw4920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4920 raw4920Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw4920 raw4920Labels = mixedMoment B raw4920step0 raw4920step0Labels := by
      have hz : ∀ j, raw4920 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4920step0 = (fun i j => raw4920 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4920step0 raw4920; decide +kernel
      have hl : raw4920step0Labels = raw4920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4920 raw4920Labels permutation434 hz
    mixedMoment B raw4920step0 raw4920step0Labels = mixedMoment B raw4920step1 raw4920step1Labels := by
      have ha : raw4920step1 = (fun i j => raw4920step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4920step1 raw4920step0; decide +kernel
      have hl : raw4920step1Labels = raw4920step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4920step0 raw4920step0Labels permutation44 permutation2
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw4921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4921 raw4921Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw4921 raw4921Labels = mixedMoment B raw4921step0 raw4921step0Labels := by
      have hz : ∀ j, raw4921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4921step0 = (fun i j => raw4921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4921step0 raw4921; decide +kernel
      have hl : raw4921step0Labels = raw4921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4921 raw4921Labels permutation434 hz
    mixedMoment B raw4921step0 raw4921step0Labels = mixedMoment B raw4921step1 raw4921step1Labels := by
      have ha : raw4921step1 = (fun i j => raw4921step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4921step1 raw4921step0; decide +kernel
      have hl : raw4921step1Labels = raw4921step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4921step0 raw4921step0Labels permutation44 permutation2
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw4922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw4922step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4922 raw4922Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw4922 raw4922Labels = mixedMoment B raw4922step0 raw4922step0Labels := by
      have hz : ∀ j, raw4922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4922step0 = (fun i j => raw4922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4922step0 raw4922; decide +kernel
      have hl : raw4922step0Labels = raw4922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4922 raw4922Labels permutation434 hz
    mixedMoment B raw4922step0 raw4922step0Labels = mixedMoment B raw4922step1 raw4922step1Labels := by
      have hz : ∀ j, raw4922step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4922step1 = (fun i j => raw4922step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4922step1 raw4922step0; decide +kernel
      have hl : raw4922step1Labels = raw4922step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4922step0 raw4922step0Labels permutation80 hz
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw4923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4923step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4923step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4923step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4923 raw4923Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw4923 raw4923Labels = mixedMoment B raw4923step0 raw4923step0Labels := by
      have hz : ∀ j, raw4923 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4923step0 = (fun i j => raw4923 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4923step0 raw4923; decide +kernel
      have hl : raw4923step0Labels = raw4923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4923 raw4923Labels permutation434 hz
    mixedMoment B raw4923step0 raw4923step0Labels = mixedMoment B raw4923step1 raw4923step1Labels := by
      have hz : ∀ j, raw4923step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4923step1 = (fun i j => raw4923step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4923step1 raw4923step0; decide +kernel
      have hl : raw4923step1Labels = raw4923step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4923step0 raw4923step0Labels permutation80 hz
    mixedMoment B raw4923step1 raw4923step1Labels = mixedMoment B raw4923step2 raw4923step2Labels := by
      have ha : raw4923step2 = (fun i j => raw4923step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4923step2 raw4923step1; decide +kernel
      have hl : raw4923step2Labels = raw4923step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4923step1 raw4923step1Labels permutation10 permutation3
    mixedMoment B raw4923step2 raw4923step2Labels = mixedMoment B raw4923step3 raw4923step3Labels := by
      have ha : raw4923step3 = raw4923step2 := by apply Matrix.ext; unfold raw4923step3 raw4923step2; decide +kernel
      have hl : raw4923step2Labels = labelEmbedding6 ∘ raw4923step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4923step2 raw4923step2Labels raw4923step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

def raw4924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4924step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4924step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4924step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4924step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4924 raw4924Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw4924 raw4924Labels = mixedMoment B raw4924step0 raw4924step0Labels := by
      have hz : ∀ j, raw4924 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4924step0 = (fun i j => raw4924 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4924step0 raw4924; decide +kernel
      have hl : raw4924step0Labels = raw4924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4924 raw4924Labels permutation434 hz
    mixedMoment B raw4924step0 raw4924step0Labels = mixedMoment B raw4924step1 raw4924step1Labels := by
      have ha : raw4924step1 = (fun i j => raw4924step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4924step1 raw4924step0; decide +kernel
      have hl : raw4924step1Labels = raw4924step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4924step0 raw4924step0Labels permutation139 permutation3
    mixedMoment B raw4924step1 raw4924step1Labels = mixedMoment B raw4924step2 raw4924step2Labels := by
      have ha : raw4924step2 = -raw4924step1 := by apply Matrix.ext; change ∀ i j, raw4924step2 i j = -(raw4924step1 i j); unfold raw4924step2 raw4924step1; decide +kernel
      have hl : raw4924step2Labels = raw4924step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4924step2 raw4924step2Labels = mixedMoment B raw4924step3 raw4924step3Labels := by
      have ha : raw4924step3 = raw4924step2 := by apply Matrix.ext; unfold raw4924step3 raw4924step2; decide +kernel
      have hl : raw4924step2Labels = labelEmbedding6 ∘ raw4924step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4924step2 raw4924step2Labels raw4924step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw4925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4925step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4925step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4925step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4925step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4925 raw4925Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw4925 raw4925Labels = mixedMoment B raw4925step0 raw4925step0Labels := by
      have hz : ∀ j, raw4925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4925step0 = (fun i j => raw4925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4925step0 raw4925; decide +kernel
      have hl : raw4925step0Labels = raw4925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4925 raw4925Labels permutation346 hz
    mixedMoment B raw4925step0 raw4925step0Labels = mixedMoment B raw4925step1 raw4925step1Labels := by
      have ha : raw4925step1 = (fun i j => raw4925step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4925step1 raw4925step0; decide +kernel
      have hl : raw4925step1Labels = raw4925step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4925step0 raw4925step0Labels permutation139 permutation3
    mixedMoment B raw4925step1 raw4925step1Labels = mixedMoment B raw4925step2 raw4925step2Labels := by
      have ha : raw4925step2 = -raw4925step1 := by apply Matrix.ext; change ∀ i j, raw4925step2 i j = -(raw4925step1 i j); unfold raw4925step2 raw4925step1; decide +kernel
      have hl : raw4925step2Labels = raw4925step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4925step2 raw4925step2Labels = mixedMoment B raw4925step3 raw4925step3Labels := by
      have ha : raw4925step3 = raw4925step2 := by apply Matrix.ext; unfold raw4925step3 raw4925step2; decide +kernel
      have hl : raw4925step2Labels = labelEmbedding6 ∘ raw4925step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4925step2 raw4925step2Labels raw4925step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw4926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![3, -2, -1]]
def raw4926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4926step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw4926step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4926step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw4926step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4926 raw4926Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw4926 raw4926Labels = mixedMoment B raw4926step0 raw4926step0Labels := by
      have hz : ∀ j, raw4926 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4926step0 = (fun i j => raw4926 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4926step0 raw4926; decide +kernel
      have hl : raw4926step0Labels = raw4926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4926 raw4926Labels permutation434 hz
    mixedMoment B raw4926step0 raw4926step0Labels = mixedMoment B raw4926step1 raw4926step1Labels := by
      have hz : ∀ j, raw4926step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4926step1 = (fun i j => raw4926step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4926step1 raw4926step0; decide +kernel
      have hl : raw4926step1Labels = raw4926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4926step0 raw4926step0Labels permutation80 hz
    mixedMoment B raw4926step1 raw4926step1Labels = mixedMoment B raw4926step2 raw4926step2Labels := by
      have ha : raw4926step2 = (fun i j => raw4926step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4926step2 raw4926step1; decide +kernel
      have hl : raw4926step2Labels = raw4926step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4926step1 raw4926step1Labels permutation10 permutation3
    mixedMoment B raw4926step2 raw4926step2Labels = mixedMoment B raw4926step3 raw4926step3Labels := by
      have ha : raw4926step3 = raw4926step2 := by apply Matrix.ext; unfold raw4926step3 raw4926step2; decide +kernel
      have hl : raw4926step2Labels = labelEmbedding6 ∘ raw4926step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4926step2 raw4926step2Labels raw4926step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5021 node5021Labels := by rfl

def raw4927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4927step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4927 raw4927Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw4927 raw4927Labels = mixedMoment B raw4927step0 raw4927step0Labels := by
      have hz : ∀ j, raw4927 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4927step0 = (fun i j => raw4927 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4927step0 raw4927; decide +kernel
      have hl : raw4927step0Labels = raw4927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4927 raw4927Labels permutation434 hz
    mixedMoment B raw4927step0 raw4927step0Labels = mixedMoment B raw4927step1 raw4927step1Labels := by
      have ha : raw4927step1 = (fun i j => raw4927step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4927step1 raw4927step0; decide +kernel
      have hl : raw4927step1Labels = raw4927step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4927step0 raw4927step0Labels permutation44 permutation3
    mixedMoment B raw4927step1 raw4927step1Labels = mixedMoment B raw4927step2 raw4927step2Labels := by
      have ha : raw4927step2 = raw4927step1 := by apply Matrix.ext; unfold raw4927step2 raw4927step1; decide +kernel
      have hl : raw4927step1Labels = labelEmbedding6 ∘ raw4927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4927step1 raw4927step1Labels raw4927step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

def raw4928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4928step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4928step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4928step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4928step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4928 raw4928Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw4928 raw4928Labels = mixedMoment B raw4928step0 raw4928step0Labels := by
      have hz : ∀ j, raw4928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4928step0 = (fun i j => raw4928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4928step0 raw4928; decide +kernel
      have hl : raw4928step0Labels = raw4928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4928 raw4928Labels permutation434 hz
    mixedMoment B raw4928step0 raw4928step0Labels = mixedMoment B raw4928step1 raw4928step1Labels := by
      have ha : raw4928step1 = (fun i j => raw4928step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4928step1 raw4928step0; decide +kernel
      have hl : raw4928step1Labels = raw4928step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4928step0 raw4928step0Labels permutation145 permutation3
    mixedMoment B raw4928step1 raw4928step1Labels = mixedMoment B raw4928step2 raw4928step2Labels := by
      have ha : raw4928step2 = -raw4928step1 := by apply Matrix.ext; change ∀ i j, raw4928step2 i j = -(raw4928step1 i j); unfold raw4928step2 raw4928step1; decide +kernel
      have hl : raw4928step2Labels = raw4928step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4928step2 raw4928step2Labels = mixedMoment B raw4928step3 raw4928step3Labels := by
      have ha : raw4928step3 = raw4928step2 := by apply Matrix.ext; unfold raw4928step3 raw4928step2; decide +kernel
      have hl : raw4928step2Labels = labelEmbedding6 ∘ raw4928step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4928step2 raw4928step2Labels raw4928step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw4929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4929step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4929 raw4929Labels = mixedMoment B node5047 node5047Labels := by
  calc
    mixedMoment B raw4929 raw4929Labels = mixedMoment B raw4929step0 raw4929step0Labels := by
      have ha : raw4929step0 = (fun i j => raw4929 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4929step0 raw4929; decide +kernel
      have hl : raw4929step0Labels = raw4929Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4929 raw4929Labels permutation212 permutation3
    mixedMoment B raw4929step0 raw4929step0Labels = mixedMoment B raw4929step1 raw4929step1Labels := by
      have ha : raw4929step1 = raw4929step0 := by apply Matrix.ext; unfold raw4929step1 raw4929step0; decide +kernel
      have hl : raw4929step0Labels = labelEmbedding6 ∘ raw4929step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4929step0 raw4929step0Labels raw4929step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5047 node5047Labels := by rfl

def raw4930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4930step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4930step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4930 raw4930Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw4930 raw4930Labels = mixedMoment B raw4930step0 raw4930step0Labels := by
      have hz : ∀ j, raw4930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4930step0 = (fun i j => raw4930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4930step0 raw4930; decide +kernel
      have hl : raw4930step0Labels = raw4930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4930 raw4930Labels permutation434 hz
    mixedMoment B raw4930step0 raw4930step0Labels = mixedMoment B raw4930step1 raw4930step1Labels := by
      have ha : raw4930step1 = (fun i j => raw4930step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4930step1 raw4930step0; decide +kernel
      have hl : raw4930step1Labels = raw4930step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4930step0 raw4930step0Labels permutation44 permutation3
    mixedMoment B raw4930step1 raw4930step1Labels = mixedMoment B raw4930step2 raw4930step2Labels := by
      have ha : raw4930step2 = raw4930step1 := by apply Matrix.ext; unfold raw4930step2 raw4930step1; decide +kernel
      have hl : raw4930step1Labels = labelEmbedding6 ∘ raw4930step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4930step1 raw4930step1Labels raw4930step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw4931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4931step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4931step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4931 raw4931Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw4931 raw4931Labels = mixedMoment B raw4931step0 raw4931step0Labels := by
      have hz : ∀ j, raw4931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4931step0 = (fun i j => raw4931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4931step0 raw4931; decide +kernel
      have hl : raw4931step0Labels = raw4931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4931 raw4931Labels permutation346 hz
    mixedMoment B raw4931step0 raw4931step0Labels = mixedMoment B raw4931step1 raw4931step1Labels := by
      have ha : raw4931step1 = (fun i j => raw4931step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4931step1 raw4931step0; decide +kernel
      have hl : raw4931step1Labels = raw4931step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4931step0 raw4931step0Labels permutation44 permutation3
    mixedMoment B raw4931step1 raw4931step1Labels = mixedMoment B raw4931step2 raw4931step2Labels := by
      have ha : raw4931step2 = raw4931step1 := by apply Matrix.ext; unfold raw4931step2 raw4931step1; decide +kernel
      have hl : raw4931step1Labels = labelEmbedding6 ∘ raw4931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4931step1 raw4931step1Labels raw4931step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

def raw4932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4932step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4932step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4932step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4932step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4932 raw4932Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw4932 raw4932Labels = mixedMoment B raw4932step0 raw4932step0Labels := by
      have hz : ∀ j, raw4932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4932step0 = (fun i j => raw4932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4932step0 raw4932; decide +kernel
      have hl : raw4932step0Labels = raw4932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4932 raw4932Labels permutation346 hz
    mixedMoment B raw4932step0 raw4932step0Labels = mixedMoment B raw4932step1 raw4932step1Labels := by
      have ha : raw4932step1 = (fun i j => raw4932step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4932step1 raw4932step0; decide +kernel
      have hl : raw4932step1Labels = raw4932step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4932step0 raw4932step0Labels permutation145 permutation3
    mixedMoment B raw4932step1 raw4932step1Labels = mixedMoment B raw4932step2 raw4932step2Labels := by
      have ha : raw4932step2 = -raw4932step1 := by apply Matrix.ext; change ∀ i j, raw4932step2 i j = -(raw4932step1 i j); unfold raw4932step2 raw4932step1; decide +kernel
      have hl : raw4932step2Labels = raw4932step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4932step2 raw4932step2Labels = mixedMoment B raw4932step3 raw4932step3Labels := by
      have ha : raw4932step3 = raw4932step2 := by apply Matrix.ext; unfold raw4932step3 raw4932step2; decide +kernel
      have hl : raw4932step2Labels = labelEmbedding6 ∘ raw4932step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4932step2 raw4932step2Labels raw4932step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw4933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4933step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4933 raw4933Labels = mixedMoment B node5047 node5047Labels := by
  calc
    mixedMoment B raw4933 raw4933Labels = mixedMoment B raw4933step0 raw4933step0Labels := by
      have ha : raw4933step0 = (fun i j => raw4933 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4933step0 raw4933; decide +kernel
      have hl : raw4933step0Labels = raw4933Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4933 raw4933Labels permutation188 permutation3
    mixedMoment B raw4933step0 raw4933step0Labels = mixedMoment B raw4933step1 raw4933step1Labels := by
      have ha : raw4933step1 = raw4933step0 := by apply Matrix.ext; unfold raw4933step1 raw4933step0; decide +kernel
      have hl : raw4933step0Labels = labelEmbedding6 ∘ raw4933step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4933step0 raw4933step0Labels raw4933step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5047 node5047Labels := by rfl

def raw4934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4934step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4934step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4934step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4934 raw4934Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw4934 raw4934Labels = mixedMoment B raw4934step0 raw4934step0Labels := by
      have hz : ∀ j, raw4934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4934step0 = (fun i j => raw4934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4934step0 raw4934; decide +kernel
      have hl : raw4934step0Labels = raw4934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4934 raw4934Labels permutation346 hz
    mixedMoment B raw4934step0 raw4934step0Labels = mixedMoment B raw4934step1 raw4934step1Labels := by
      have ha : raw4934step1 = (fun i j => raw4934step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4934step1 raw4934step0; decide +kernel
      have hl : raw4934step1Labels = raw4934step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4934step0 raw4934step0Labels permutation44 permutation3
    mixedMoment B raw4934step1 raw4934step1Labels = mixedMoment B raw4934step2 raw4934step2Labels := by
      have ha : raw4934step2 = raw4934step1 := by apply Matrix.ext; unfold raw4934step2 raw4934step1; decide +kernel
      have hl : raw4934step1Labels = labelEmbedding6 ∘ raw4934step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4934step1 raw4934step1Labels raw4934step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw4935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw4935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4935step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4935step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4935step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4935 raw4935Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw4935 raw4935Labels = mixedMoment B raw4935step0 raw4935step0Labels := by
      have hz : ∀ j, raw4935 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4935step0 = (fun i j => raw4935 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4935step0 raw4935; decide +kernel
      have hl : raw4935step0Labels = raw4935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4935 raw4935Labels permutation434 hz
    mixedMoment B raw4935step0 raw4935step0Labels = mixedMoment B raw4935step1 raw4935step1Labels := by
      have hz : ∀ j, raw4935step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4935step1 = (fun i j => raw4935step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4935step1 raw4935step0; decide +kernel
      have hl : raw4935step1Labels = raw4935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4935step0 raw4935step0Labels permutation80 hz
    mixedMoment B raw4935step1 raw4935step1Labels = mixedMoment B raw4935step2 raw4935step2Labels := by
      have ha : raw4935step2 = (fun i j => raw4935step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4935step2 raw4935step1; decide +kernel
      have hl : raw4935step2Labels = raw4935step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4935step1 raw4935step1Labels permutation8 permutation3
    mixedMoment B raw4935step2 raw4935step2Labels = mixedMoment B raw4935step3 raw4935step3Labels := by
      have ha : raw4935step3 = raw4935step2 := by apply Matrix.ext; unfold raw4935step3 raw4935step2; decide +kernel
      have hl : raw4935step2Labels = labelEmbedding6 ∘ raw4935step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4935step2 raw4935step2Labels raw4935step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw4936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw4936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw4936step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4936step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw4936step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4936 raw4936Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw4936 raw4936Labels = mixedMoment B raw4936step0 raw4936step0Labels := by
      have hz : ∀ j, raw4936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4936step0 = (fun i j => raw4936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4936step0 raw4936; decide +kernel
      have hl : raw4936step0Labels = raw4936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4936 raw4936Labels permutation434 hz
    mixedMoment B raw4936step0 raw4936step0Labels = mixedMoment B raw4936step1 raw4936step1Labels := by
      have hz : ∀ j, raw4936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4936step1 = (fun i j => raw4936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4936step1 raw4936step0; decide +kernel
      have hl : raw4936step1Labels = raw4936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4936step0 raw4936step0Labels permutation80 hz
    mixedMoment B raw4936step1 raw4936step1Labels = mixedMoment B raw4936step2 raw4936step2Labels := by
      have ha : raw4936step2 = (fun i j => raw4936step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4936step2 raw4936step1; decide +kernel
      have hl : raw4936step2Labels = raw4936step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4936step1 raw4936step1Labels permutation8 permutation3
    mixedMoment B raw4936step2 raw4936step2Labels = mixedMoment B raw4936step3 raw4936step3Labels := by
      have ha : raw4936step3 = raw4936step2 := by apply Matrix.ext; unfold raw4936step3 raw4936step2; decide +kernel
      have hl : raw4936step2Labels = labelEmbedding6 ∘ raw4936step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4936step2 raw4936step2Labels raw4936step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw4937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4937step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4937 raw4937Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw4937 raw4937Labels = mixedMoment B raw4937step0 raw4937step0Labels := by
      have hz : ∀ j, raw4937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4937step0 = (fun i j => raw4937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4937step0 raw4937; decide +kernel
      have hl : raw4937step0Labels = raw4937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4937 raw4937Labels permutation434 hz
    mixedMoment B raw4937step0 raw4937step0Labels = mixedMoment B raw4937step1 raw4937step1Labels := by
      have ha : raw4937step1 = (fun i j => raw4937step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4937step1 raw4937step0; decide +kernel
      have hl : raw4937step1Labels = raw4937step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4937step0 raw4937step0Labels permutation38 permutation3
    mixedMoment B raw4937step1 raw4937step1Labels = mixedMoment B raw4937step2 raw4937step2Labels := by
      have ha : raw4937step2 = raw4937step1 := by apply Matrix.ext; unfold raw4937step2 raw4937step1; decide +kernel
      have hl : raw4937step1Labels = labelEmbedding6 ∘ raw4937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4937step1 raw4937step1Labels raw4937step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw4938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4938step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4938 raw4938Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw4938 raw4938Labels = mixedMoment B raw4938step0 raw4938step0Labels := by
      have hz : ∀ j, raw4938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4938step0 = (fun i j => raw4938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4938step0 raw4938; decide +kernel
      have hl : raw4938step0Labels = raw4938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4938 raw4938Labels permutation346 hz
    mixedMoment B raw4938step0 raw4938step0Labels = mixedMoment B raw4938step1 raw4938step1Labels := by
      have ha : raw4938step1 = (fun i j => raw4938step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4938step1 raw4938step0; decide +kernel
      have hl : raw4938step1Labels = raw4938step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4938step0 raw4938step0Labels permutation38 permutation3
    mixedMoment B raw4938step1 raw4938step1Labels = mixedMoment B raw4938step2 raw4938step2Labels := by
      have ha : raw4938step2 = raw4938step1 := by apply Matrix.ext; unfold raw4938step2 raw4938step1; decide +kernel
      have hl : raw4938step1Labels = labelEmbedding6 ∘ raw4938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4938step1 raw4938step1Labels raw4938step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw4939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw4939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw4939step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw4939step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4939 raw4939Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw4939 raw4939Labels = mixedMoment B raw4939step0 raw4939step0Labels := by
      have hz : ∀ j, raw4939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4939step0 = (fun i j => raw4939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4939step0 raw4939; decide +kernel
      have hl : raw4939step0Labels = raw4939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4939 raw4939Labels permutation434 hz
    mixedMoment B raw4939step0 raw4939step0Labels = mixedMoment B raw4939step1 raw4939step1Labels := by
      have hz : ∀ j, raw4939step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4939step1 = (fun i j => raw4939step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4939step1 raw4939step0; decide +kernel
      have hl : raw4939step1Labels = raw4939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4939step0 raw4939step0Labels permutation80 hz
    mixedMoment B raw4939step1 raw4939step1Labels = mixedMoment B raw4939step2 raw4939step2Labels := by
      have ha : raw4939step2 = (fun i j => raw4939step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4939step2 raw4939step1; decide +kernel
      have hl : raw4939step2Labels = raw4939step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4939step1 raw4939step1Labels permutation10 permutation3
    mixedMoment B raw4939step2 raw4939step2Labels = mixedMoment B raw4939step3 raw4939step3Labels := by
      have ha : raw4939step3 = raw4939step2 := by apply Matrix.ext; unfold raw4939step3 raw4939step2; decide +kernel
      have hl : raw4939step2Labels = labelEmbedding6 ∘ raw4939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4939step2 raw4939step2Labels raw4939step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw4940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![4, -3, -1]]
def raw4940step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4940step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4940step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4940step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4940step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4940step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4940 raw4940Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw4940 raw4940Labels = mixedMoment B raw4940step0 raw4940step0Labels := by
      have hz : ∀ j, raw4940 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4940step0 = (fun i j => raw4940 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4940step0 raw4940; decide +kernel
      have hl : raw4940step0Labels = raw4940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4940 raw4940Labels permutation434 hz
    mixedMoment B raw4940step0 raw4940step0Labels = mixedMoment B raw4940step1 raw4940step1Labels := by
      have hz : ∀ j, raw4940step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4940step1 = (fun i j => raw4940step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4940step1 raw4940step0; decide +kernel
      have hl : raw4940step1Labels = raw4940step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4940step0 raw4940step0Labels permutation80 hz
    mixedMoment B raw4940step1 raw4940step1Labels = mixedMoment B raw4940step2 raw4940step2Labels := by
      have ha : raw4940step2 = (fun i j => raw4940step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4940step2 raw4940step1; decide +kernel
      have hl : raw4940step2Labels = raw4940step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4940step1 raw4940step1Labels permutation31 permutation3
    mixedMoment B raw4940step2 raw4940step2Labels = mixedMoment B raw4940step3 raw4940step3Labels := by
      have ha : raw4940step3 = -raw4940step2 := by apply Matrix.ext; change ∀ i j, raw4940step3 i j = -(raw4940step2 i j); unfold raw4940step3 raw4940step2; decide +kernel
      have hl : raw4940step3Labels = raw4940step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4940step3 raw4940step3Labels = mixedMoment B raw4940step4 raw4940step4Labels := by
      have ha : raw4940step4 = raw4940step3 := by apply Matrix.ext; unfold raw4940step4 raw4940step3; decide +kernel
      have hl : raw4940step3Labels = labelEmbedding6 ∘ raw4940step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4940step3 raw4940step3Labels raw4940step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw4941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4941step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4941step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4941step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4941step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4941 raw4941Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw4941 raw4941Labels = mixedMoment B raw4941step0 raw4941step0Labels := by
      have hz : ∀ j, raw4941 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4941step0 = (fun i j => raw4941 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4941step0 raw4941; decide +kernel
      have hl : raw4941step0Labels = raw4941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4941 raw4941Labels permutation434 hz
    mixedMoment B raw4941step0 raw4941step0Labels = mixedMoment B raw4941step1 raw4941step1Labels := by
      have ha : raw4941step1 = (fun i j => raw4941step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4941step1 raw4941step0; decide +kernel
      have hl : raw4941step1Labels = raw4941step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4941step0 raw4941step0Labels permutation139 permutation3
    mixedMoment B raw4941step1 raw4941step1Labels = mixedMoment B raw4941step2 raw4941step2Labels := by
      have ha : raw4941step2 = -raw4941step1 := by apply Matrix.ext; change ∀ i j, raw4941step2 i j = -(raw4941step1 i j); unfold raw4941step2 raw4941step1; decide +kernel
      have hl : raw4941step2Labels = raw4941step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4941step2 raw4941step2Labels = mixedMoment B raw4941step3 raw4941step3Labels := by
      have ha : raw4941step3 = raw4941step2 := by apply Matrix.ext; unfold raw4941step3 raw4941step2; decide +kernel
      have hl : raw4941step2Labels = labelEmbedding6 ∘ raw4941step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4941step2 raw4941step2Labels raw4941step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

def raw4942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4942step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4942step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4942step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4942step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4942 raw4942Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw4942 raw4942Labels = mixedMoment B raw4942step0 raw4942step0Labels := by
      have hz : ∀ j, raw4942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4942step0 = (fun i j => raw4942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4942step0 raw4942; decide +kernel
      have hl : raw4942step0Labels = raw4942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4942 raw4942Labels permutation346 hz
    mixedMoment B raw4942step0 raw4942step0Labels = mixedMoment B raw4942step1 raw4942step1Labels := by
      have ha : raw4942step1 = (fun i j => raw4942step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4942step1 raw4942step0; decide +kernel
      have hl : raw4942step1Labels = raw4942step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4942step0 raw4942step0Labels permutation139 permutation3
    mixedMoment B raw4942step1 raw4942step1Labels = mixedMoment B raw4942step2 raw4942step2Labels := by
      have ha : raw4942step2 = -raw4942step1 := by apply Matrix.ext; change ∀ i j, raw4942step2 i j = -(raw4942step1 i j); unfold raw4942step2 raw4942step1; decide +kernel
      have hl : raw4942step2Labels = raw4942step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4942step2 raw4942step2Labels = mixedMoment B raw4942step3 raw4942step3Labels := by
      have ha : raw4942step3 = raw4942step2 := by apply Matrix.ext; unfold raw4942step3 raw4942step2; decide +kernel
      have hl : raw4942step2Labels = labelEmbedding6 ∘ raw4942step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4942step2 raw4942step2Labels raw4942step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

def raw4943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![4, -3, -1]]
def raw4943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw4943step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4943step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4943step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4943step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4943 raw4943Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw4943 raw4943Labels = mixedMoment B raw4943step0 raw4943step0Labels := by
      have hz : ∀ j, raw4943 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4943step0 = (fun i j => raw4943 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4943step0 raw4943; decide +kernel
      have hl : raw4943step0Labels = raw4943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4943 raw4943Labels permutation434 hz
    mixedMoment B raw4943step0 raw4943step0Labels = mixedMoment B raw4943step1 raw4943step1Labels := by
      have hz : ∀ j, raw4943step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4943step1 = (fun i j => raw4943step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4943step1 raw4943step0; decide +kernel
      have hl : raw4943step1Labels = raw4943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4943step0 raw4943step0Labels permutation80 hz
    mixedMoment B raw4943step1 raw4943step1Labels = mixedMoment B raw4943step2 raw4943step2Labels := by
      have ha : raw4943step2 = (fun i j => raw4943step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4943step2 raw4943step1; decide +kernel
      have hl : raw4943step2Labels = raw4943step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4943step1 raw4943step1Labels permutation29 permutation3
    mixedMoment B raw4943step2 raw4943step2Labels = mixedMoment B raw4943step3 raw4943step3Labels := by
      have ha : raw4943step3 = -raw4943step2 := by apply Matrix.ext; change ∀ i j, raw4943step3 i j = -(raw4943step2 i j); unfold raw4943step3 raw4943step2; decide +kernel
      have hl : raw4943step3Labels = raw4943step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4943step3 raw4943step3Labels = mixedMoment B raw4943step4 raw4943step4Labels := by
      have ha : raw4943step4 = raw4943step3 := by apply Matrix.ext; unfold raw4943step4 raw4943step3; decide +kernel
      have hl : raw4943step3Labels = labelEmbedding6 ∘ raw4943step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4943step3 raw4943step3Labels raw4943step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

def raw4944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw4944step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw4944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4944 raw4944Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw4944 raw4944Labels = mixedMoment B raw4944step0 raw4944step0Labels := by
      have hz : ∀ j, raw4944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4944step0 = (fun i j => raw4944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4944step0 raw4944; decide +kernel
      have hl : raw4944step0Labels = raw4944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4944 raw4944Labels permutation434 hz
    mixedMoment B raw4944step0 raw4944step0Labels = mixedMoment B raw4944step1 raw4944step1Labels := by
      have hz : ∀ j, raw4944step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4944step1 = (fun i j => raw4944step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4944step1 raw4944step0; decide +kernel
      have hl : raw4944step1Labels = raw4944step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4944step0 raw4944step0Labels permutation80 hz
    mixedMoment B raw4944step1 raw4944step1Labels = mixedMoment B raw4944step2 raw4944step2Labels := by
      have ha : raw4944step2 = (fun i j => raw4944step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4944step2 raw4944step1; decide +kernel
      have hl : raw4944step2Labels = raw4944step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4944step1 raw4944step1Labels permutation10 permutation3
    _ = mixedMoment B node4014 node4014Labels := by rfl

def raw4945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4945step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4945 raw4945Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw4945 raw4945Labels = mixedMoment B raw4945step0 raw4945step0Labels := by
      have hz : ∀ j, raw4945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4945step0 = (fun i j => raw4945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4945step0 raw4945; decide +kernel
      have hl : raw4945step0Labels = raw4945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4945 raw4945Labels permutation434 hz
    mixedMoment B raw4945step0 raw4945step0Labels = mixedMoment B raw4945step1 raw4945step1Labels := by
      have hz : ∀ j, raw4945step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4945step1 = (fun i j => raw4945step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4945step1 raw4945step0; decide +kernel
      have hl : raw4945step1Labels = raw4945step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4945step0 raw4945step0Labels permutation80 hz
    mixedMoment B raw4945step1 raw4945step1Labels = mixedMoment B raw4945step2 raw4945step2Labels := by
      have ha : raw4945step2 = (fun i j => raw4945step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4945step2 raw4945step1; decide +kernel
      have hl : raw4945step2Labels = raw4945step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4945step1 raw4945step1Labels permutation10 permutation3
    _ = mixedMoment B node1009 node1009Labels := by rfl

def raw4946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4946 raw4946Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw4946 raw4946Labels = mixedMoment B raw4946step0 raw4946step0Labels := by
      have hz : ∀ j, raw4946 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4946step0 = (fun i j => raw4946 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4946step0 raw4946; decide +kernel
      have hl : raw4946step0Labels = raw4946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4946 raw4946Labels permutation434 hz
    mixedMoment B raw4946step0 raw4946step0Labels = mixedMoment B raw4946step1 raw4946step1Labels := by
      have ha : raw4946step1 = (fun i j => raw4946step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4946step1 raw4946step0; decide +kernel
      have hl : raw4946step1Labels = raw4946step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4946step0 raw4946step0Labels permutation139 permutation3
    mixedMoment B raw4946step1 raw4946step1Labels = mixedMoment B raw4946step2 raw4946step2Labels := by
      have ha : raw4946step2 = -raw4946step1 := by apply Matrix.ext; change ∀ i j, raw4946step2 i j = -(raw4946step1 i j); unfold raw4946step2 raw4946step1; decide +kernel
      have hl : raw4946step2Labels = raw4946step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw4947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4947 raw4947Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw4947 raw4947Labels = mixedMoment B raw4947step0 raw4947step0Labels := by
      have hz : ∀ j, raw4947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4947step0 = (fun i j => raw4947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4947step0 raw4947; decide +kernel
      have hl : raw4947step0Labels = raw4947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4947 raw4947Labels permutation346 hz
    mixedMoment B raw4947step0 raw4947step0Labels = mixedMoment B raw4947step1 raw4947step1Labels := by
      have ha : raw4947step1 = (fun i j => raw4947step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4947step1 raw4947step0; decide +kernel
      have hl : raw4947step1Labels = raw4947step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4947step0 raw4947step0Labels permutation139 permutation3
    mixedMoment B raw4947step1 raw4947step1Labels = mixedMoment B raw4947step2 raw4947step2Labels := by
      have ha : raw4947step2 = -raw4947step1 := by apply Matrix.ext; change ∀ i j, raw4947step2 i j = -(raw4947step1 i j); unfold raw4947step2 raw4947step1; decide +kernel
      have hl : raw4947step2Labels = raw4947step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw4948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![3, -2, -1]]
def raw4948step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw4948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4948 raw4948Labels = mixedMoment B node2407 node2407Labels := by
  calc
    mixedMoment B raw4948 raw4948Labels = mixedMoment B raw4948step0 raw4948step0Labels := by
      have hz : ∀ j, raw4948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4948step0 = (fun i j => raw4948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4948step0 raw4948; decide +kernel
      have hl : raw4948step0Labels = raw4948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4948 raw4948Labels permutation434 hz
    mixedMoment B raw4948step0 raw4948step0Labels = mixedMoment B raw4948step1 raw4948step1Labels := by
      have hz : ∀ j, raw4948step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4948step1 = (fun i j => raw4948step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4948step1 raw4948step0; decide +kernel
      have hl : raw4948step1Labels = raw4948step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4948step0 raw4948step0Labels permutation80 hz
    mixedMoment B raw4948step1 raw4948step1Labels = mixedMoment B raw4948step2 raw4948step2Labels := by
      have ha : raw4948step2 = (fun i j => raw4948step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4948step2 raw4948step1; decide +kernel
      have hl : raw4948step2Labels = raw4948step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4948step1 raw4948step1Labels permutation10 permutation3
    _ = mixedMoment B node2407 node2407Labels := by rfl

def raw4949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4949 raw4949Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw4949 raw4949Labels = mixedMoment B raw4949step0 raw4949step0Labels := by
      have hz : ∀ j, raw4949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4949step0 = (fun i j => raw4949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4949step0 raw4949; decide +kernel
      have hl : raw4949step0Labels = raw4949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4949 raw4949Labels permutation434 hz
    mixedMoment B raw4949step0 raw4949step0Labels = mixedMoment B raw4949step1 raw4949step1Labels := by
      have ha : raw4949step1 = (fun i j => raw4949step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4949step1 raw4949step0; decide +kernel
      have hl : raw4949step1Labels = raw4949step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4949step0 raw4949step0Labels permutation44 permutation3
    _ = mixedMoment B node982 node982Labels := by rfl

def raw4950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4950 raw4950Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw4950 raw4950Labels = mixedMoment B raw4950step0 raw4950step0Labels := by
      have hz : ∀ j, raw4950 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4950step0 = (fun i j => raw4950 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4950step0 raw4950; decide +kernel
      have hl : raw4950step0Labels = raw4950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4950 raw4950Labels permutation434 hz
    mixedMoment B raw4950step0 raw4950step0Labels = mixedMoment B raw4950step1 raw4950step1Labels := by
      have ha : raw4950step1 = (fun i j => raw4950step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4950step1 raw4950step0; decide +kernel
      have hl : raw4950step1Labels = raw4950step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4950step0 raw4950step0Labels permutation145 permutation3
    mixedMoment B raw4950step1 raw4950step1Labels = mixedMoment B raw4950step2 raw4950step2Labels := by
      have ha : raw4950step2 = -raw4950step1 := by apply Matrix.ext; change ∀ i j, raw4950step2 i j = -(raw4950step1 i j); unfold raw4950step2 raw4950step1; decide +kernel
      have hl : raw4950step2Labels = raw4950step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw4951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4951 raw4951Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw4951 raw4951Labels = mixedMoment B raw4951step0 raw4951step0Labels := by
      have ha : raw4951step0 = (fun i j => raw4951 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4951step0 raw4951; decide +kernel
      have hl : raw4951step0Labels = raw4951Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4951 raw4951Labels permutation212 permutation3
    _ = mixedMoment B node2449 node2449Labels := by rfl

def raw4952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4952 raw4952Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw4952 raw4952Labels = mixedMoment B raw4952step0 raw4952step0Labels := by
      have hz : ∀ j, raw4952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4952step0 = (fun i j => raw4952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4952step0 raw4952; decide +kernel
      have hl : raw4952step0Labels = raw4952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4952 raw4952Labels permutation434 hz
    mixedMoment B raw4952step0 raw4952step0Labels = mixedMoment B raw4952step1 raw4952step1Labels := by
      have ha : raw4952step1 = (fun i j => raw4952step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4952step1 raw4952step0; decide +kernel
      have hl : raw4952step1Labels = raw4952step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4952step0 raw4952step0Labels permutation44 permutation3
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw4953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4953 raw4953Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw4953 raw4953Labels = mixedMoment B raw4953step0 raw4953step0Labels := by
      have hz : ∀ j, raw4953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4953step0 = (fun i j => raw4953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4953step0 raw4953; decide +kernel
      have hl : raw4953step0Labels = raw4953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4953 raw4953Labels permutation346 hz
    mixedMoment B raw4953step0 raw4953step0Labels = mixedMoment B raw4953step1 raw4953step1Labels := by
      have ha : raw4953step1 = (fun i j => raw4953step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4953step1 raw4953step0; decide +kernel
      have hl : raw4953step1Labels = raw4953step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4953step0 raw4953step0Labels permutation44 permutation3
    _ = mixedMoment B node982 node982Labels := by rfl

def raw4954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4954step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4954 raw4954Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw4954 raw4954Labels = mixedMoment B raw4954step0 raw4954step0Labels := by
      have hz : ∀ j, raw4954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4954step0 = (fun i j => raw4954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4954step0 raw4954; decide +kernel
      have hl : raw4954step0Labels = raw4954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4954 raw4954Labels permutation346 hz
    mixedMoment B raw4954step0 raw4954step0Labels = mixedMoment B raw4954step1 raw4954step1Labels := by
      have ha : raw4954step1 = (fun i j => raw4954step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4954step1 raw4954step0; decide +kernel
      have hl : raw4954step1Labels = raw4954step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4954step0 raw4954step0Labels permutation145 permutation3
    mixedMoment B raw4954step1 raw4954step1Labels = mixedMoment B raw4954step2 raw4954step2Labels := by
      have ha : raw4954step2 = -raw4954step1 := by apply Matrix.ext; change ∀ i j, raw4954step2 i j = -(raw4954step1 i j); unfold raw4954step2 raw4954step1; decide +kernel
      have hl : raw4954step2Labels = raw4954step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw4955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4955 raw4955Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw4955 raw4955Labels = mixedMoment B raw4955step0 raw4955step0Labels := by
      have ha : raw4955step0 = (fun i j => raw4955 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4955step0 raw4955; decide +kernel
      have hl : raw4955step0Labels = raw4955Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4955 raw4955Labels permutation188 permutation3
    _ = mixedMoment B node2449 node2449Labels := by rfl

def raw4956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4956step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4956 raw4956Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw4956 raw4956Labels = mixedMoment B raw4956step0 raw4956step0Labels := by
      have hz : ∀ j, raw4956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4956step0 = (fun i j => raw4956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4956step0 raw4956; decide +kernel
      have hl : raw4956step0Labels = raw4956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4956 raw4956Labels permutation346 hz
    mixedMoment B raw4956step0 raw4956step0Labels = mixedMoment B raw4956step1 raw4956step1Labels := by
      have ha : raw4956step1 = (fun i j => raw4956step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4956step1 raw4956step0; decide +kernel
      have hl : raw4956step1Labels = raw4956step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4956step0 raw4956step0Labels permutation44 permutation3
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw4957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw4957step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4957 raw4957Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw4957 raw4957Labels = mixedMoment B raw4957step0 raw4957step0Labels := by
      have hz : ∀ j, raw4957 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4957step0 = (fun i j => raw4957 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4957step0 raw4957; decide +kernel
      have hl : raw4957step0Labels = raw4957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4957 raw4957Labels permutation434 hz
    mixedMoment B raw4957step0 raw4957step0Labels = mixedMoment B raw4957step1 raw4957step1Labels := by
      have hz : ∀ j, raw4957step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4957step1 = (fun i j => raw4957step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4957step1 raw4957step0; decide +kernel
      have hl : raw4957step1Labels = raw4957step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4957step0 raw4957step0Labels permutation80 hz
    mixedMoment B raw4957step1 raw4957step1Labels = mixedMoment B raw4957step2 raw4957step2Labels := by
      have ha : raw4957step2 = (fun i j => raw4957step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4957step2 raw4957step1; decide +kernel
      have hl : raw4957step2Labels = raw4957step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4957step1 raw4957step1Labels permutation8 permutation3
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw4958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw4958step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw4958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4958 raw4958Labels = mixedMoment B node2598 node2598Labels := by
  calc
    mixedMoment B raw4958 raw4958Labels = mixedMoment B raw4958step0 raw4958step0Labels := by
      have hz : ∀ j, raw4958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4958step0 = (fun i j => raw4958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4958step0 raw4958; decide +kernel
      have hl : raw4958step0Labels = raw4958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4958 raw4958Labels permutation434 hz
    mixedMoment B raw4958step0 raw4958step0Labels = mixedMoment B raw4958step1 raw4958step1Labels := by
      have hz : ∀ j, raw4958step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4958step1 = (fun i j => raw4958step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4958step1 raw4958step0; decide +kernel
      have hl : raw4958step1Labels = raw4958step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4958step0 raw4958step0Labels permutation80 hz
    mixedMoment B raw4958step1 raw4958step1Labels = mixedMoment B raw4958step2 raw4958step2Labels := by
      have ha : raw4958step2 = (fun i j => raw4958step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4958step2 raw4958step1; decide +kernel
      have hl : raw4958step2Labels = raw4958step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4958step1 raw4958step1Labels permutation8 permutation3
    _ = mixedMoment B node2598 node2598Labels := by rfl

def raw4959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4959 raw4959Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw4959 raw4959Labels = mixedMoment B raw4959step0 raw4959step0Labels := by
      have hz : ∀ j, raw4959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4959step0 = (fun i j => raw4959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4959step0 raw4959; decide +kernel
      have hl : raw4959step0Labels = raw4959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4959 raw4959Labels permutation434 hz
    mixedMoment B raw4959step0 raw4959step0Labels = mixedMoment B raw4959step1 raw4959step1Labels := by
      have ha : raw4959step1 = (fun i j => raw4959step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4959step1 raw4959step0; decide +kernel
      have hl : raw4959step1Labels = raw4959step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4959step0 raw4959step0Labels permutation38 permutation3
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw4960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4960 raw4960Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw4960 raw4960Labels = mixedMoment B raw4960step0 raw4960step0Labels := by
      have hz : ∀ j, raw4960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4960step0 = (fun i j => raw4960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4960step0 raw4960; decide +kernel
      have hl : raw4960step0Labels = raw4960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4960 raw4960Labels permutation346 hz
    mixedMoment B raw4960step0 raw4960step0Labels = mixedMoment B raw4960step1 raw4960step1Labels := by
      have ha : raw4960step1 = (fun i j => raw4960step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4960step1 raw4960step0; decide +kernel
      have hl : raw4960step1Labels = raw4960step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4960step0 raw4960step0Labels permutation38 permutation3
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw4961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw4961step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw4961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4961 raw4961Labels = mixedMoment B node986 node986Labels := by
  calc
    mixedMoment B raw4961 raw4961Labels = mixedMoment B raw4961step0 raw4961step0Labels := by
      have hz : ∀ j, raw4961 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4961step0 = (fun i j => raw4961 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4961step0 raw4961; decide +kernel
      have hl : raw4961step0Labels = raw4961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4961 raw4961Labels permutation434 hz
    mixedMoment B raw4961step0 raw4961step0Labels = mixedMoment B raw4961step1 raw4961step1Labels := by
      have hz : ∀ j, raw4961step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4961step1 = (fun i j => raw4961step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4961step1 raw4961step0; decide +kernel
      have hl : raw4961step1Labels = raw4961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4961step0 raw4961step0Labels permutation80 hz
    mixedMoment B raw4961step1 raw4961step1Labels = mixedMoment B raw4961step2 raw4961step2Labels := by
      have ha : raw4961step2 = (fun i j => raw4961step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4961step2 raw4961step1; decide +kernel
      have hl : raw4961step2Labels = raw4961step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4961step1 raw4961step1Labels permutation10 permutation3
    _ = mixedMoment B node986 node986Labels := by rfl

def raw4962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![4, -3, -1]]
def raw4962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4962step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4962 raw4962Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw4962 raw4962Labels = mixedMoment B raw4962step0 raw4962step0Labels := by
      have hz : ∀ j, raw4962 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4962step0 = (fun i j => raw4962 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4962step0 raw4962; decide +kernel
      have hl : raw4962step0Labels = raw4962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4962 raw4962Labels permutation434 hz
    mixedMoment B raw4962step0 raw4962step0Labels = mixedMoment B raw4962step1 raw4962step1Labels := by
      have hz : ∀ j, raw4962step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4962step1 = (fun i j => raw4962step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4962step1 raw4962step0; decide +kernel
      have hl : raw4962step1Labels = raw4962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4962step0 raw4962step0Labels permutation80 hz
    mixedMoment B raw4962step1 raw4962step1Labels = mixedMoment B raw4962step2 raw4962step2Labels := by
      have ha : raw4962step2 = (fun i j => raw4962step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4962step2 raw4962step1; decide +kernel
      have hl : raw4962step2Labels = raw4962step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4962step1 raw4962step1Labels permutation31 permutation3
    mixedMoment B raw4962step2 raw4962step2Labels = mixedMoment B raw4962step3 raw4962step3Labels := by
      have ha : raw4962step3 = -raw4962step2 := by apply Matrix.ext; change ∀ i j, raw4962step3 i j = -(raw4962step2 i j); unfold raw4962step3 raw4962step2; decide +kernel
      have hl : raw4962step3Labels = raw4962step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw4963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4963 raw4963Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw4963 raw4963Labels = mixedMoment B raw4963step0 raw4963step0Labels := by
      have hz : ∀ j, raw4963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4963step0 = (fun i j => raw4963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4963step0 raw4963; decide +kernel
      have hl : raw4963step0Labels = raw4963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4963 raw4963Labels permutation434 hz
    mixedMoment B raw4963step0 raw4963step0Labels = mixedMoment B raw4963step1 raw4963step1Labels := by
      have ha : raw4963step1 = (fun i j => raw4963step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4963step1 raw4963step0; decide +kernel
      have hl : raw4963step1Labels = raw4963step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4963step0 raw4963step0Labels permutation139 permutation3
    mixedMoment B raw4963step1 raw4963step1Labels = mixedMoment B raw4963step2 raw4963step2Labels := by
      have ha : raw4963step2 = -raw4963step1 := by apply Matrix.ext; change ∀ i j, raw4963step2 i j = -(raw4963step1 i j); unfold raw4963step2 raw4963step1; decide +kernel
      have hl : raw4963step2Labels = raw4963step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node982 node982Labels := by rfl

def raw4964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4964 raw4964Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw4964 raw4964Labels = mixedMoment B raw4964step0 raw4964step0Labels := by
      have hz : ∀ j, raw4964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4964step0 = (fun i j => raw4964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4964step0 raw4964; decide +kernel
      have hl : raw4964step0Labels = raw4964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4964 raw4964Labels permutation346 hz
    mixedMoment B raw4964step0 raw4964step0Labels = mixedMoment B raw4964step1 raw4964step1Labels := by
      have ha : raw4964step1 = (fun i j => raw4964step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4964step1 raw4964step0; decide +kernel
      have hl : raw4964step1Labels = raw4964step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4964step0 raw4964step0Labels permutation139 permutation3
    mixedMoment B raw4964step1 raw4964step1Labels = mixedMoment B raw4964step2 raw4964step2Labels := by
      have ha : raw4964step2 = -raw4964step1 := by apply Matrix.ext; change ∀ i j, raw4964step2 i j = -(raw4964step1 i j); unfold raw4964step2 raw4964step1; decide +kernel
      have hl : raw4964step2Labels = raw4964step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node982 node982Labels := by rfl

def raw4965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![4, -3, -1]]
def raw4965step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw4965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4965step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4965step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4965 raw4965Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw4965 raw4965Labels = mixedMoment B raw4965step0 raw4965step0Labels := by
      have hz : ∀ j, raw4965 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4965step0 = (fun i j => raw4965 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4965step0 raw4965; decide +kernel
      have hl : raw4965step0Labels = raw4965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4965 raw4965Labels permutation434 hz
    mixedMoment B raw4965step0 raw4965step0Labels = mixedMoment B raw4965step1 raw4965step1Labels := by
      have hz : ∀ j, raw4965step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4965step1 = (fun i j => raw4965step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4965step1 raw4965step0; decide +kernel
      have hl : raw4965step1Labels = raw4965step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4965step0 raw4965step0Labels permutation80 hz
    mixedMoment B raw4965step1 raw4965step1Labels = mixedMoment B raw4965step2 raw4965step2Labels := by
      have ha : raw4965step2 = (fun i j => raw4965step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4965step2 raw4965step1; decide +kernel
      have hl : raw4965step2Labels = raw4965step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4965step1 raw4965step1Labels permutation29 permutation3
    mixedMoment B raw4965step2 raw4965step2Labels = mixedMoment B raw4965step3 raw4965step3Labels := by
      have ha : raw4965step3 = -raw4965step2 := by apply Matrix.ext; change ∀ i j, raw4965step3 i j = -(raw4965step2 i j); unfold raw4965step3 raw4965step2; decide +kernel
      have hl : raw4965step3Labels = raw4965step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1009 node1009Labels := by rfl

def raw4966 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4966step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, -2, 3]]
def raw4966step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4966step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw4966step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4966step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4966step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4966step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4966step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4966 raw4966Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw4966 raw4966Labels = mixedMoment B raw4966step0 raw4966step0Labels := by
      have hz : ∀ j, raw4966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4966step0 = (fun i j => raw4966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4966step0 raw4966; decide +kernel
      have hl : raw4966step0Labels = raw4966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4966 raw4966Labels permutation434 hz
    mixedMoment B raw4966step0 raw4966step0Labels = mixedMoment B raw4966step1 raw4966step1Labels := by
      have hz : ∀ j, raw4966step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4966step1 = (fun i j => raw4966step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4966step1 raw4966step0; decide +kernel
      have hl : raw4966step1Labels = raw4966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4966step0 raw4966step0Labels permutation80 hz
    mixedMoment B raw4966step1 raw4966step1Labels = mixedMoment B raw4966step2 raw4966step2Labels := by
      have hz : ∀ j, raw4966step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4966step2 = (fun i j => raw4966step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4966step2 raw4966step1; decide +kernel
      have hl : raw4966step2Labels = raw4966step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4966step1 raw4966step1Labels permutation14 hz
    mixedMoment B raw4966step2 raw4966step2Labels = mixedMoment B raw4966step3 raw4966step3Labels := by
      have ha : raw4966step3 = (fun i j => raw4966step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4966step3 raw4966step2; decide +kernel
      have hl : raw4966step3Labels = raw4966step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4966step2 raw4966step2Labels permutation7 permutation6
    mixedMoment B raw4966step3 raw4966step3Labels = mixedMoment B raw4966step4 raw4966step4Labels := by
      have ha : raw4966step4 = -raw4966step3 := by apply Matrix.ext; change ∀ i j, raw4966step4 i j = -(raw4966step3 i j); unfold raw4966step4 raw4966step3; decide +kernel
      have hl : raw4966step4Labels = raw4966step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4966step4 raw4966step4Labels = mixedMoment B raw4966step5 raw4966step5Labels := by
      have ha : raw4966step5 = raw4966step4 := by apply Matrix.ext; unfold raw4966step5 raw4966step4; decide +kernel
      have hl : raw4966step4Labels = labelEmbedding9 ∘ raw4966step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4966step4 raw4966step4Labels raw4966step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw4967 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4967step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4967step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4967 raw4967Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4967 raw4967Labels = mixedMoment B raw4967step0 raw4967step0Labels := by
      have hz : ∀ j, raw4967 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4967step0 = (fun i j => raw4967 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4967step0 raw4967; decide +kernel
      have hl : raw4967step0Labels = raw4967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4967 raw4967Labels permutation434 hz
    mixedMoment B raw4967step0 raw4967step0Labels = mixedMoment B raw4967step1 raw4967step1Labels := by
      have ha : raw4967step1 = (fun i j => raw4967step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4967step1 raw4967step0; decide +kernel
      have hl : raw4967step1Labels = raw4967step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4967step0 raw4967step0Labels permutation137 permutation6
    mixedMoment B raw4967step1 raw4967step1Labels = mixedMoment B raw4967step2 raw4967step2Labels := by
      have ha : raw4967step2 = -raw4967step1 := by apply Matrix.ext; change ∀ i j, raw4967step2 i j = -(raw4967step1 i j); unfold raw4967step2 raw4967step1; decide +kernel
      have hl : raw4967step2Labels = raw4967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4967step2 raw4967step2Labels = mixedMoment B raw4967step3 raw4967step3Labels := by
      have ha : raw4967step3 = raw4967step2 := by apply Matrix.ext; unfold raw4967step3 raw4967step2; decide +kernel
      have hl : raw4967step2Labels = labelEmbedding9 ∘ raw4967step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4967step2 raw4967step2Labels raw4967step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw4968 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4968step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4968step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4968step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4968step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4968 raw4968Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4968 raw4968Labels = mixedMoment B raw4968step0 raw4968step0Labels := by
      have hz : ∀ j, raw4968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4968step0 = (fun i j => raw4968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4968step0 raw4968; decide +kernel
      have hl : raw4968step0Labels = raw4968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4968 raw4968Labels permutation346 hz
    mixedMoment B raw4968step0 raw4968step0Labels = mixedMoment B raw4968step1 raw4968step1Labels := by
      have ha : raw4968step1 = (fun i j => raw4968step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4968step1 raw4968step0; decide +kernel
      have hl : raw4968step1Labels = raw4968step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4968step0 raw4968step0Labels permutation137 permutation6
    mixedMoment B raw4968step1 raw4968step1Labels = mixedMoment B raw4968step2 raw4968step2Labels := by
      have ha : raw4968step2 = -raw4968step1 := by apply Matrix.ext; change ∀ i j, raw4968step2 i j = -(raw4968step1 i j); unfold raw4968step2 raw4968step1; decide +kernel
      have hl : raw4968step2Labels = raw4968step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4968step2 raw4968step2Labels = mixedMoment B raw4968step3 raw4968step3Labels := by
      have ha : raw4968step3 = raw4968step2 := by apply Matrix.ext; unfold raw4968step3 raw4968step2; decide +kernel
      have hl : raw4968step2Labels = labelEmbedding9 ∘ raw4968step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4968step2 raw4968step2Labels raw4968step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw4969 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4969step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4969step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw4969step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4969step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4969step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4969step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4969step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4969 raw4969Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw4969 raw4969Labels = mixedMoment B raw4969step0 raw4969step0Labels := by
      have hz : ∀ j, raw4969 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4969step0 = (fun i j => raw4969 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4969step0 raw4969; decide +kernel
      have hl : raw4969step0Labels = raw4969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4969 raw4969Labels permutation434 hz
    mixedMoment B raw4969step0 raw4969step0Labels = mixedMoment B raw4969step1 raw4969step1Labels := by
      have hz : ∀ j, raw4969step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4969step1 = (fun i j => raw4969step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4969step1 raw4969step0; decide +kernel
      have hl : raw4969step1Labels = raw4969step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4969step0 raw4969step0Labels permutation80 hz
    mixedMoment B raw4969step1 raw4969step1Labels = mixedMoment B raw4969step2 raw4969step2Labels := by
      have ha : raw4969step2 = (fun i j => raw4969step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4969step2 raw4969step1; decide +kernel
      have hl : raw4969step2Labels = raw4969step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4969step1 raw4969step1Labels permutation29 permutation6
    mixedMoment B raw4969step2 raw4969step2Labels = mixedMoment B raw4969step3 raw4969step3Labels := by
      have ha : raw4969step3 = -raw4969step2 := by apply Matrix.ext; change ∀ i j, raw4969step3 i j = -(raw4969step2 i j); unfold raw4969step3 raw4969step2; decide +kernel
      have hl : raw4969step3Labels = raw4969step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4969step3 raw4969step3Labels = mixedMoment B raw4969step4 raw4969step4Labels := by
      have ha : raw4969step4 = raw4969step3 := by apply Matrix.ext; unfold raw4969step4 raw4969step3; decide +kernel
      have hl : raw4969step3Labels = labelEmbedding9 ∘ raw4969step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4969step3 raw4969step3Labels raw4969step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw4970 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4970step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4970step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4970step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4970step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4970step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4970 raw4970Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4970 raw4970Labels = mixedMoment B raw4970step0 raw4970step0Labels := by
      have hz : ∀ j, raw4970 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4970step0 = (fun i j => raw4970 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4970step0 raw4970; decide +kernel
      have hl : raw4970step0Labels = raw4970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4970 raw4970Labels permutation434 hz
    mixedMoment B raw4970step0 raw4970step0Labels = mixedMoment B raw4970step1 raw4970step1Labels := by
      have hz : ∀ j, raw4970step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4970step1 = (fun i j => raw4970step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4970step1 raw4970step0; decide +kernel
      have hl : raw4970step1Labels = raw4970step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4970step0 raw4970step0Labels permutation80 hz
    mixedMoment B raw4970step1 raw4970step1Labels = mixedMoment B raw4970step2 raw4970step2Labels := by
      have ha : raw4970step2 = (fun i j => raw4970step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4970step2 raw4970step1; decide +kernel
      have hl : raw4970step2Labels = raw4970step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4970step1 raw4970step1Labels permutation8 permutation7
    mixedMoment B raw4970step2 raw4970step2Labels = mixedMoment B raw4970step3 raw4970step3Labels := by
      have ha : raw4970step3 = raw4970step2 := by apply Matrix.ext; unfold raw4970step3 raw4970step2; decide +kernel
      have hl : raw4970step2Labels = labelEmbedding10 ∘ raw4970step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4970step2 raw4970step2Labels raw4970step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4971 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw4971step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4971step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4971step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4971step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4971step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4971 raw4971Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw4971 raw4971Labels = mixedMoment B raw4971step0 raw4971step0Labels := by
      have hz : ∀ j, raw4971 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4971step0 = (fun i j => raw4971 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4971step0 raw4971; decide +kernel
      have hl : raw4971step0Labels = raw4971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4971 raw4971Labels permutation434 hz
    mixedMoment B raw4971step0 raw4971step0Labels = mixedMoment B raw4971step1 raw4971step1Labels := by
      have hz : ∀ j, raw4971step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4971step1 = (fun i j => raw4971step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4971step1 raw4971step0; decide +kernel
      have hl : raw4971step1Labels = raw4971step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4971step0 raw4971step0Labels permutation80 hz
    mixedMoment B raw4971step1 raw4971step1Labels = mixedMoment B raw4971step2 raw4971step2Labels := by
      have ha : raw4971step2 = (fun i j => raw4971step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4971step2 raw4971step1; decide +kernel
      have hl : raw4971step2Labels = raw4971step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4971step1 raw4971step1Labels permutation10 permutation4
    mixedMoment B raw4971step2 raw4971step2Labels = mixedMoment B raw4971step3 raw4971step3Labels := by
      have ha : raw4971step3 = -raw4971step2 := by apply Matrix.ext; change ∀ i j, raw4971step3 i j = -(raw4971step2 i j); unfold raw4971step3 raw4971step2; decide +kernel
      have hl : raw4971step3Labels = raw4971step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4971step3 raw4971step3Labels = mixedMoment B raw4971step4 raw4971step4Labels := by
      have ha : raw4971step4 = raw4971step3 := by apply Matrix.ext; unfold raw4971step4 raw4971step3; decide +kernel
      have hl : raw4971step3Labels = labelEmbedding7 ∘ raw4971step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4971step3 raw4971step3Labels raw4971step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw4972 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4972step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4972step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4972step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4972step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4972 raw4972Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw4972 raw4972Labels = mixedMoment B raw4972step0 raw4972step0Labels := by
      have hz : ∀ j, raw4972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4972step0 = (fun i j => raw4972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4972step0 raw4972; decide +kernel
      have hl : raw4972step0Labels = raw4972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4972 raw4972Labels permutation434 hz
    mixedMoment B raw4972step0 raw4972step0Labels = mixedMoment B raw4972step1 raw4972step1Labels := by
      have ha : raw4972step1 = (fun i j => raw4972step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4972step1 raw4972step0; decide +kernel
      have hl : raw4972step1Labels = raw4972step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4972step0 raw4972step0Labels permutation137 permutation6
    mixedMoment B raw4972step1 raw4972step1Labels = mixedMoment B raw4972step2 raw4972step2Labels := by
      have ha : raw4972step2 = -raw4972step1 := by apply Matrix.ext; change ∀ i j, raw4972step2 i j = -(raw4972step1 i j); unfold raw4972step2 raw4972step1; decide +kernel
      have hl : raw4972step2Labels = raw4972step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4972step2 raw4972step2Labels = mixedMoment B raw4972step3 raw4972step3Labels := by
      have ha : raw4972step3 = raw4972step2 := by apply Matrix.ext; unfold raw4972step3 raw4972step2; decide +kernel
      have hl : raw4972step2Labels = labelEmbedding9 ∘ raw4972step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4972step2 raw4972step2Labels raw4972step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw4973 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4973step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4973step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4973 raw4973Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw4973 raw4973Labels = mixedMoment B raw4973step0 raw4973step0Labels := by
      have hz : ∀ j, raw4973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4973step0 = (fun i j => raw4973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4973step0 raw4973; decide +kernel
      have hl : raw4973step0Labels = raw4973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4973 raw4973Labels permutation346 hz
    mixedMoment B raw4973step0 raw4973step0Labels = mixedMoment B raw4973step1 raw4973step1Labels := by
      have ha : raw4973step1 = (fun i j => raw4973step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4973step1 raw4973step0; decide +kernel
      have hl : raw4973step1Labels = raw4973step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4973step0 raw4973step0Labels permutation137 permutation6
    mixedMoment B raw4973step1 raw4973step1Labels = mixedMoment B raw4973step2 raw4973step2Labels := by
      have ha : raw4973step2 = -raw4973step1 := by apply Matrix.ext; change ∀ i j, raw4973step2 i j = -(raw4973step1 i j); unfold raw4973step2 raw4973step1; decide +kernel
      have hl : raw4973step2Labels = raw4973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4973step2 raw4973step2Labels = mixedMoment B raw4973step3 raw4973step3Labels := by
      have ha : raw4973step3 = raw4973step2 := by apply Matrix.ext; unfold raw4973step3 raw4973step2; decide +kernel
      have hl : raw4973step2Labels = labelEmbedding9 ∘ raw4973step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4973step2 raw4973step2Labels raw4973step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw4974 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4974step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw4974step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4974step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw4974step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4974 raw4974Labels = mixedMoment B node5235 node5235Labels := by
  calc
    mixedMoment B raw4974 raw4974Labels = mixedMoment B raw4974step0 raw4974step0Labels := by
      have hz : ∀ j, raw4974 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4974step0 = (fun i j => raw4974 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4974step0 raw4974; decide +kernel
      have hl : raw4974step0Labels = raw4974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4974 raw4974Labels permutation434 hz
    mixedMoment B raw4974step0 raw4974step0Labels = mixedMoment B raw4974step1 raw4974step1Labels := by
      have hz : ∀ j, raw4974step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4974step1 = (fun i j => raw4974step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4974step1 raw4974step0; decide +kernel
      have hl : raw4974step1Labels = raw4974step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4974step0 raw4974step0Labels permutation80 hz
    mixedMoment B raw4974step1 raw4974step1Labels = mixedMoment B raw4974step2 raw4974step2Labels := by
      have ha : raw4974step2 = (fun i j => raw4974step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4974step2 raw4974step1; decide +kernel
      have hl : raw4974step2Labels = raw4974step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4974step1 raw4974step1Labels permutation10 permutation6
    mixedMoment B raw4974step2 raw4974step2Labels = mixedMoment B raw4974step3 raw4974step3Labels := by
      have ha : raw4974step3 = raw4974step2 := by apply Matrix.ext; unfold raw4974step3 raw4974step2; decide +kernel
      have hl : raw4974step2Labels = labelEmbedding9 ∘ raw4974step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4974step2 raw4974step2Labels raw4974step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5235 node5235Labels := by rfl

def raw4975 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4975step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4975step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4975 raw4975Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw4975 raw4975Labels = mixedMoment B raw4975step0 raw4975step0Labels := by
      have hz : ∀ j, raw4975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4975step0 = (fun i j => raw4975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4975step0 raw4975; decide +kernel
      have hl : raw4975step0Labels = raw4975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4975 raw4975Labels permutation434 hz
    mixedMoment B raw4975step0 raw4975step0Labels = mixedMoment B raw4975step1 raw4975step1Labels := by
      have hz : ∀ j, raw4975step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4975step1 = (fun i j => raw4975step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4975step1 raw4975step0; decide +kernel
      have hl : raw4975step1Labels = raw4975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4975step0 raw4975step0Labels permutation80 hz
    mixedMoment B raw4975step1 raw4975step1Labels = mixedMoment B raw4975step2 raw4975step2Labels := by
      have ha : raw4975step2 = (fun i j => raw4975step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4975step2 raw4975step1; decide +kernel
      have hl : raw4975step2Labels = raw4975step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4975step1 raw4975step1Labels permutation10 permutation6
    mixedMoment B raw4975step2 raw4975step2Labels = mixedMoment B raw4975step3 raw4975step3Labels := by
      have ha : raw4975step3 = raw4975step2 := by apply Matrix.ext; unfold raw4975step3 raw4975step2; decide +kernel
      have hl : raw4975step2Labels = labelEmbedding9 ∘ raw4975step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4975step2 raw4975step2Labels raw4975step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw4976 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4976step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4976step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4976step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4976step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4976step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4976 raw4976Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw4976 raw4976Labels = mixedMoment B raw4976step0 raw4976step0Labels := by
      have hz : ∀ j, raw4976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4976step0 = (fun i j => raw4976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4976step0 raw4976; decide +kernel
      have hl : raw4976step0Labels = raw4976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4976 raw4976Labels permutation434 hz
    mixedMoment B raw4976step0 raw4976step0Labels = mixedMoment B raw4976step1 raw4976step1Labels := by
      have ha : raw4976step1 = (fun i j => raw4976step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4976step1 raw4976step0; decide +kernel
      have hl : raw4976step1Labels = raw4976step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4976step0 raw4976step0Labels permutation44 permutation4
    mixedMoment B raw4976step1 raw4976step1Labels = mixedMoment B raw4976step2 raw4976step2Labels := by
      have ha : raw4976step2 = -raw4976step1 := by apply Matrix.ext; change ∀ i j, raw4976step2 i j = -(raw4976step1 i j); unfold raw4976step2 raw4976step1; decide +kernel
      have hl : raw4976step2Labels = raw4976step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4976step2 raw4976step2Labels = mixedMoment B raw4976step3 raw4976step3Labels := by
      have ha : raw4976step3 = raw4976step2 := by apply Matrix.ext; unfold raw4976step3 raw4976step2; decide +kernel
      have hl : raw4976step2Labels = labelEmbedding7 ∘ raw4976step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4976step2 raw4976step2Labels raw4976step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw4977 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4977step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4977step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4977 raw4977Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4977 raw4977Labels = mixedMoment B raw4977step0 raw4977step0Labels := by
      have hz : ∀ j, raw4977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4977step0 = (fun i j => raw4977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4977step0 raw4977; decide +kernel
      have hl : raw4977step0Labels = raw4977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4977 raw4977Labels permutation434 hz
    mixedMoment B raw4977step0 raw4977step0Labels = mixedMoment B raw4977step1 raw4977step1Labels := by
      have hz : ∀ j, raw4977step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4977step1 = (fun i j => raw4977step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4977step1 raw4977step0; decide +kernel
      have hl : raw4977step1Labels = raw4977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4977step0 raw4977step0Labels permutation56 hz
    mixedMoment B raw4977step1 raw4977step1Labels = mixedMoment B raw4977step2 raw4977step2Labels := by
      have ha : raw4977step2 = (fun i j => raw4977step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4977step2 raw4977step1; decide +kernel
      have hl : raw4977step2Labels = raw4977step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4977step1 raw4977step1Labels permutation10 permutation6
    mixedMoment B raw4977step2 raw4977step2Labels = mixedMoment B raw4977step3 raw4977step3Labels := by
      have ha : raw4977step3 = raw4977step2 := by apply Matrix.ext; unfold raw4977step3 raw4977step2; decide +kernel
      have hl : raw4977step2Labels = labelEmbedding9 ∘ raw4977step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4977step2 raw4977step2Labels raw4977step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4978 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4978step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4978 raw4978Labels = mixedMoment B node5239 node5239Labels := by
  calc
    mixedMoment B raw4978 raw4978Labels = mixedMoment B raw4978step0 raw4978step0Labels := by
      have ha : raw4978step0 = (fun i j => raw4978 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4978step0 raw4978; decide +kernel
      have hl : raw4978step0Labels = raw4978Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4978 raw4978Labels permutation212 permutation6
    mixedMoment B raw4978step0 raw4978step0Labels = mixedMoment B raw4978step1 raw4978step1Labels := by
      have ha : raw4978step1 = raw4978step0 := by apply Matrix.ext; unfold raw4978step1 raw4978step0; decide +kernel
      have hl : raw4978step0Labels = labelEmbedding9 ∘ raw4978step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4978step0 raw4978step0Labels raw4978step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5239 node5239Labels := by rfl

def raw4979 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4979step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4979step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4979 raw4979Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw4979 raw4979Labels = mixedMoment B raw4979step0 raw4979step0Labels := by
      have hz : ∀ j, raw4979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4979step0 = (fun i j => raw4979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4979step0 raw4979; decide +kernel
      have hl : raw4979step0Labels = raw4979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4979 raw4979Labels permutation434 hz
    mixedMoment B raw4979step0 raw4979step0Labels = mixedMoment B raw4979step1 raw4979step1Labels := by
      have ha : raw4979step1 = (fun i j => raw4979step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4979step1 raw4979step0; decide +kernel
      have hl : raw4979step1Labels = raw4979step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4979step0 raw4979step0Labels permutation44 permutation6
    mixedMoment B raw4979step1 raw4979step1Labels = mixedMoment B raw4979step2 raw4979step2Labels := by
      have ha : raw4979step2 = raw4979step1 := by apply Matrix.ext; unfold raw4979step2 raw4979step1; decide +kernel
      have hl : raw4979step1Labels = labelEmbedding9 ∘ raw4979step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4979step1 raw4979step1Labels raw4979step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw4980 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4980step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4980step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4980 raw4980Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4980 raw4980Labels = mixedMoment B raw4980step0 raw4980step0Labels := by
      have hz : ∀ j, raw4980 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4980step0 = (fun i j => raw4980 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4980step0 raw4980; decide +kernel
      have hl : raw4980step0Labels = raw4980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4980 raw4980Labels permutation434 hz
    mixedMoment B raw4980step0 raw4980step0Labels = mixedMoment B raw4980step1 raw4980step1Labels := by
      have ha : raw4980step1 = (fun i j => raw4980step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4980step1 raw4980step0; decide +kernel
      have hl : raw4980step1Labels = raw4980step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4980step0 raw4980step0Labels permutation44 permutation6
    mixedMoment B raw4980step1 raw4980step1Labels = mixedMoment B raw4980step2 raw4980step2Labels := by
      have ha : raw4980step2 = raw4980step1 := by apply Matrix.ext; unfold raw4980step2 raw4980step1; decide +kernel
      have hl : raw4980step1Labels = labelEmbedding9 ∘ raw4980step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4980step1 raw4980step1Labels raw4980step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw4981 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4981step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4981step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4981step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4981step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4981 raw4981Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw4981 raw4981Labels = mixedMoment B raw4981step0 raw4981step0Labels := by
      have hz : ∀ j, raw4981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4981step0 = (fun i j => raw4981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4981step0 raw4981; decide +kernel
      have hl : raw4981step0Labels = raw4981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4981 raw4981Labels permutation346 hz
    mixedMoment B raw4981step0 raw4981step0Labels = mixedMoment B raw4981step1 raw4981step1Labels := by
      have ha : raw4981step1 = (fun i j => raw4981step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4981step1 raw4981step0; decide +kernel
      have hl : raw4981step1Labels = raw4981step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4981step0 raw4981step0Labels permutation44 permutation4
    mixedMoment B raw4981step1 raw4981step1Labels = mixedMoment B raw4981step2 raw4981step2Labels := by
      have ha : raw4981step2 = -raw4981step1 := by apply Matrix.ext; change ∀ i j, raw4981step2 i j = -(raw4981step1 i j); unfold raw4981step2 raw4981step1; decide +kernel
      have hl : raw4981step2Labels = raw4981step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4981step2 raw4981step2Labels = mixedMoment B raw4981step3 raw4981step3Labels := by
      have ha : raw4981step3 = raw4981step2 := by apply Matrix.ext; unfold raw4981step3 raw4981step2; decide +kernel
      have hl : raw4981step2Labels = labelEmbedding7 ∘ raw4981step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4981step2 raw4981step2Labels raw4981step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw4982 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4982step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4982step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4982step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4982 raw4982Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4982 raw4982Labels = mixedMoment B raw4982step0 raw4982step0Labels := by
      have hz : ∀ j, raw4982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4982step0 = (fun i j => raw4982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4982step0 raw4982; decide +kernel
      have hl : raw4982step0Labels = raw4982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4982 raw4982Labels permutation346 hz
    mixedMoment B raw4982step0 raw4982step0Labels = mixedMoment B raw4982step1 raw4982step1Labels := by
      have hz : ∀ j, raw4982step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4982step1 = (fun i j => raw4982step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4982step1 raw4982step0; decide +kernel
      have hl : raw4982step1Labels = raw4982step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4982step0 raw4982step0Labels permutation56 hz
    mixedMoment B raw4982step1 raw4982step1Labels = mixedMoment B raw4982step2 raw4982step2Labels := by
      have ha : raw4982step2 = (fun i j => raw4982step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4982step2 raw4982step1; decide +kernel
      have hl : raw4982step2Labels = raw4982step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4982step1 raw4982step1Labels permutation10 permutation6
    mixedMoment B raw4982step2 raw4982step2Labels = mixedMoment B raw4982step3 raw4982step3Labels := by
      have ha : raw4982step3 = raw4982step2 := by apply Matrix.ext; unfold raw4982step3 raw4982step2; decide +kernel
      have hl : raw4982step2Labels = labelEmbedding9 ∘ raw4982step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4982step2 raw4982step2Labels raw4982step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4983 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4983step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4983 raw4983Labels = mixedMoment B node5239 node5239Labels := by
  calc
    mixedMoment B raw4983 raw4983Labels = mixedMoment B raw4983step0 raw4983step0Labels := by
      have ha : raw4983step0 = (fun i j => raw4983 (permutation188 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4983step0 raw4983; decide +kernel
      have hl : raw4983step0Labels = raw4983Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4983 raw4983Labels permutation188 permutation6
    mixedMoment B raw4983step0 raw4983step0Labels = mixedMoment B raw4983step1 raw4983step1Labels := by
      have ha : raw4983step1 = raw4983step0 := by apply Matrix.ext; unfold raw4983step1 raw4983step0; decide +kernel
      have hl : raw4983step0Labels = labelEmbedding9 ∘ raw4983step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4983step0 raw4983step0Labels raw4983step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5239 node5239Labels := by rfl

def raw4984 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4984step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4984 raw4984Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw4984 raw4984Labels = mixedMoment B raw4984step0 raw4984step0Labels := by
      have hz : ∀ j, raw4984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4984step0 = (fun i j => raw4984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4984step0 raw4984; decide +kernel
      have hl : raw4984step0Labels = raw4984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4984 raw4984Labels permutation346 hz
    mixedMoment B raw4984step0 raw4984step0Labels = mixedMoment B raw4984step1 raw4984step1Labels := by
      have ha : raw4984step1 = (fun i j => raw4984step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4984step1 raw4984step0; decide +kernel
      have hl : raw4984step1Labels = raw4984step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4984step0 raw4984step0Labels permutation44 permutation6
    mixedMoment B raw4984step1 raw4984step1Labels = mixedMoment B raw4984step2 raw4984step2Labels := by
      have ha : raw4984step2 = raw4984step1 := by apply Matrix.ext; unfold raw4984step2 raw4984step1; decide +kernel
      have hl : raw4984step1Labels = labelEmbedding9 ∘ raw4984step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4984step1 raw4984step1Labels raw4984step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw4985 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4985step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4985step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4985 raw4985Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4985 raw4985Labels = mixedMoment B raw4985step0 raw4985step0Labels := by
      have hz : ∀ j, raw4985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4985step0 = (fun i j => raw4985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4985step0 raw4985; decide +kernel
      have hl : raw4985step0Labels = raw4985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4985 raw4985Labels permutation346 hz
    mixedMoment B raw4985step0 raw4985step0Labels = mixedMoment B raw4985step1 raw4985step1Labels := by
      have ha : raw4985step1 = (fun i j => raw4985step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4985step1 raw4985step0; decide +kernel
      have hl : raw4985step1Labels = raw4985step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4985step0 raw4985step0Labels permutation44 permutation6
    mixedMoment B raw4985step1 raw4985step1Labels = mixedMoment B raw4985step2 raw4985step2Labels := by
      have ha : raw4985step2 = raw4985step1 := by apply Matrix.ext; unfold raw4985step2 raw4985step1; decide +kernel
      have hl : raw4985step1Labels = labelEmbedding9 ∘ raw4985step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4985step1 raw4985step1Labels raw4985step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw4986 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4986step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw4986step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4986step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4986step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4986step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4986step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4986 raw4986Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw4986 raw4986Labels = mixedMoment B raw4986step0 raw4986step0Labels := by
      have hz : ∀ j, raw4986 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4986step0 = (fun i j => raw4986 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4986step0 raw4986; decide +kernel
      have hl : raw4986step0Labels = raw4986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4986 raw4986Labels permutation520 hz
    mixedMoment B raw4986step0 raw4986step0Labels = mixedMoment B raw4986step1 raw4986step1Labels := by
      have hz : ∀ j, raw4986step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4986step1 = (fun i j => raw4986step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4986step1 raw4986step0; decide +kernel
      have hl : raw4986step1Labels = raw4986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4986step0 raw4986step0Labels permutation104 hz
    mixedMoment B raw4986step1 raw4986step1Labels = mixedMoment B raw4986step2 raw4986step2Labels := by
      have hz : ∀ j, raw4986step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw4986step2 = (fun i j => raw4986step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw4986step2 raw4986step1; decide +kernel
      have hl : raw4986step2Labels = raw4986step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4986step1 raw4986step1Labels permutation20 hz
    mixedMoment B raw4986step2 raw4986step2Labels = mixedMoment B raw4986step3 raw4986step3Labels := by
      have ha : raw4986step3 = (fun i j => raw4986step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4986step3 raw4986step2; decide +kernel
      have hl : raw4986step3Labels = raw4986step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4986step2 raw4986step2Labels permutation2 permutation6
    mixedMoment B raw4986step3 raw4986step3Labels = mixedMoment B raw4986step4 raw4986step4Labels := by
      have ha : raw4986step4 = raw4986step3 := by apply Matrix.ext; unfold raw4986step4 raw4986step3; decide +kernel
      have hl : raw4986step3Labels = labelEmbedding9 ∘ raw4986step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4986step3 raw4986step3Labels raw4986step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw4987 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4987step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4987step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4987step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4987 raw4987Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4987 raw4987Labels = mixedMoment B raw4987step0 raw4987step0Labels := by
      have hz : ∀ j, raw4987 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4987step0 = (fun i j => raw4987 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4987step0 raw4987; decide +kernel
      have hl : raw4987step0Labels = raw4987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4987 raw4987Labels permutation520 hz
    mixedMoment B raw4987step0 raw4987step0Labels = mixedMoment B raw4987step1 raw4987step1Labels := by
      have hz : ∀ j, raw4987step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4987step1 = (fun i j => raw4987step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4987step1 raw4987step0; decide +kernel
      have hl : raw4987step1Labels = raw4987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4987step0 raw4987step0Labels permutation104 hz
    mixedMoment B raw4987step1 raw4987step1Labels = mixedMoment B raw4987step2 raw4987step2Labels := by
      have ha : raw4987step2 = (fun i j => raw4987step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4987step2 raw4987step1; decide +kernel
      have hl : raw4987step2Labels = raw4987step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4987step1 raw4987step1Labels permutation10 permutation6
    mixedMoment B raw4987step2 raw4987step2Labels = mixedMoment B raw4987step3 raw4987step3Labels := by
      have ha : raw4987step3 = raw4987step2 := by apply Matrix.ext; unfold raw4987step3 raw4987step2; decide +kernel
      have hl : raw4987step2Labels = labelEmbedding9 ∘ raw4987step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4987step2 raw4987step2Labels raw4987step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4988 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4988step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4988step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4988step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4988step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4988 raw4988Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4988 raw4988Labels = mixedMoment B raw4988step0 raw4988step0Labels := by
      have hz : ∀ j, raw4988 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4988step0 = (fun i j => raw4988 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4988step0 raw4988; decide +kernel
      have hl : raw4988step0Labels = raw4988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4988 raw4988Labels permutation520 hz
    mixedMoment B raw4988step0 raw4988step0Labels = mixedMoment B raw4988step1 raw4988step1Labels := by
      have hz : ∀ j, raw4988step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4988step1 = (fun i j => raw4988step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4988step1 raw4988step0; decide +kernel
      have hl : raw4988step1Labels = raw4988step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4988step0 raw4988step0Labels permutation80 hz
    mixedMoment B raw4988step1 raw4988step1Labels = mixedMoment B raw4988step2 raw4988step2Labels := by
      have ha : raw4988step2 = (fun i j => raw4988step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4988step2 raw4988step1; decide +kernel
      have hl : raw4988step2Labels = raw4988step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4988step1 raw4988step1Labels permutation10 permutation6
    mixedMoment B raw4988step2 raw4988step2Labels = mixedMoment B raw4988step3 raw4988step3Labels := by
      have ha : raw4988step3 = raw4988step2 := by apply Matrix.ext; unfold raw4988step3 raw4988step2; decide +kernel
      have hl : raw4988step2Labels = labelEmbedding9 ∘ raw4988step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4988step2 raw4988step2Labels raw4988step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4989 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw4989step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4989step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw4989step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4989 raw4989Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw4989 raw4989Labels = mixedMoment B raw4989step0 raw4989step0Labels := by
      have hz : ∀ j, raw4989 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4989step0 = (fun i j => raw4989 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4989step0 raw4989; decide +kernel
      have hl : raw4989step0Labels = raw4989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4989 raw4989Labels permutation434 hz
    mixedMoment B raw4989step0 raw4989step0Labels = mixedMoment B raw4989step1 raw4989step1Labels := by
      have hz : ∀ j, raw4989step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4989step1 = (fun i j => raw4989step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4989step1 raw4989step0; decide +kernel
      have hl : raw4989step1Labels = raw4989step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4989step0 raw4989step0Labels permutation80 hz
    mixedMoment B raw4989step1 raw4989step1Labels = mixedMoment B raw4989step2 raw4989step2Labels := by
      have ha : raw4989step2 = (fun i j => raw4989step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4989step2 raw4989step1; decide +kernel
      have hl : raw4989step2Labels = raw4989step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4989step1 raw4989step1Labels permutation29 permutation4
    mixedMoment B raw4989step2 raw4989step2Labels = mixedMoment B raw4989step3 raw4989step3Labels := by
      have ha : raw4989step3 = raw4989step2 := by apply Matrix.ext; unfold raw4989step3 raw4989step2; decide +kernel
      have hl : raw4989step2Labels = labelEmbedding7 ∘ raw4989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4989step2 raw4989step2Labels raw4989step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4837 node4837Labels := by rfl

def raw4990 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4990step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -3, 3]]
def raw4990step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4990step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw4990step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4990step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4990step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4990step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4990step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4990 raw4990Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw4990 raw4990Labels = mixedMoment B raw4990step0 raw4990step0Labels := by
      have hz : ∀ j, raw4990 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4990step0 = (fun i j => raw4990 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4990step0 raw4990; decide +kernel
      have hl : raw4990step0Labels = raw4990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4990 raw4990Labels permutation434 hz
    mixedMoment B raw4990step0 raw4990step0Labels = mixedMoment B raw4990step1 raw4990step1Labels := by
      have hz : ∀ j, raw4990step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4990step1 = (fun i j => raw4990step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4990step1 raw4990step0; decide +kernel
      have hl : raw4990step1Labels = raw4990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4990step0 raw4990step0Labels permutation80 hz
    mixedMoment B raw4990step1 raw4990step1Labels = mixedMoment B raw4990step2 raw4990step2Labels := by
      have hz : ∀ j, raw4990step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4990step2 = (fun i j => raw4990step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4990step2 raw4990step1; decide +kernel
      have hl : raw4990step2Labels = raw4990step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4990step1 raw4990step1Labels permutation14 hz
    mixedMoment B raw4990step2 raw4990step2Labels = mixedMoment B raw4990step3 raw4990step3Labels := by
      have ha : raw4990step3 = (fun i j => raw4990step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4990step3 raw4990step2; decide +kernel
      have hl : raw4990step3Labels = raw4990step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4990step2 raw4990step2Labels permutation7 permutation6
    mixedMoment B raw4990step3 raw4990step3Labels = mixedMoment B raw4990step4 raw4990step4Labels := by
      have ha : raw4990step4 = -raw4990step3 := by apply Matrix.ext; change ∀ i j, raw4990step4 i j = -(raw4990step3 i j); unfold raw4990step4 raw4990step3; decide +kernel
      have hl : raw4990step4Labels = raw4990step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4990step4 raw4990step4Labels = mixedMoment B raw4990step5 raw4990step5Labels := by
      have ha : raw4990step5 = raw4990step4 := by apply Matrix.ext; unfold raw4990step5 raw4990step4; decide +kernel
      have hl : raw4990step4Labels = labelEmbedding9 ∘ raw4990step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4990step4 raw4990step4Labels raw4990step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw4991 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4991step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4991 raw4991Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw4991 raw4991Labels = mixedMoment B raw4991step0 raw4991step0Labels := by
      have hz : ∀ j, raw4991 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4991step0 = (fun i j => raw4991 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4991step0 raw4991; decide +kernel
      have hl : raw4991step0Labels = raw4991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4991 raw4991Labels permutation434 hz
    mixedMoment B raw4991step0 raw4991step0Labels = mixedMoment B raw4991step1 raw4991step1Labels := by
      have ha : raw4991step1 = (fun i j => raw4991step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4991step1 raw4991step0; decide +kernel
      have hl : raw4991step1Labels = raw4991step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4991step0 raw4991step0Labels permutation137 permutation4
    mixedMoment B raw4991step1 raw4991step1Labels = mixedMoment B raw4991step2 raw4991step2Labels := by
      have ha : raw4991step2 = raw4991step1 := by apply Matrix.ext; unfold raw4991step2 raw4991step1; decide +kernel
      have hl : raw4991step1Labels = labelEmbedding7 ∘ raw4991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4991step1 raw4991step1Labels raw4991step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
