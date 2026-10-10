import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11264Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11264step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11264step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11264 raw11264Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw11264 raw11264Labels = mixedMoment B raw11264step0 raw11264step0Labels := by
      have ha : raw11264step0 = (fun i j => raw11264 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11264step0 raw11264; decide +kernel
      have hl : raw11264step0Labels = raw11264Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11264 raw11264Labels permutation212 permutation7
    mixedMoment B raw11264step0 raw11264step0Labels = mixedMoment B raw11264step1 raw11264step1Labels := by
      have ha : raw11264step1 = -raw11264step0 := by apply Matrix.ext; change ∀ i j, raw11264step1 i j = -(raw11264step0 i j); unfold raw11264step1 raw11264step0; decide +kernel
      have hl : raw11264step1Labels = raw11264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11264step1 raw11264step1Labels = mixedMoment B raw11264step2 raw11264step2Labels := by
      have ha : raw11264step2 = raw11264step1 := by apply Matrix.ext; unfold raw11264step2 raw11264step1; decide +kernel
      have hl : raw11264step1Labels = labelEmbedding1 ∘ raw11264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11264step1 raw11264step1Labels raw11264step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2720 node2720Labels := by rfl

def raw11265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11265Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11265step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11265step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11265step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11265step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11265step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11265step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11265step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11265 raw11265Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw11265 raw11265Labels = mixedMoment B raw11265step0 raw11265step0Labels := by
      have hz : ∀ j, raw11265 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11265step0 = (fun i j => raw11265 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11265step0 raw11265; decide +kernel
      have hl : raw11265step0Labels = raw11265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11265 raw11265Labels permutation520 hz
    mixedMoment B raw11265step0 raw11265step0Labels = mixedMoment B raw11265step1 raw11265step1Labels := by
      have hz : ∀ j, raw11265step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11265step1 = (fun i j => raw11265step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11265step1 raw11265step0; decide +kernel
      have hl : raw11265step1Labels = raw11265step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11265step0 raw11265step0Labels permutation104 hz
    mixedMoment B raw11265step1 raw11265step1Labels = mixedMoment B raw11265step2 raw11265step2Labels := by
      have ha : raw11265step2 = (fun i j => raw11265step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11265step2 raw11265step1; decide +kernel
      have hl : raw11265step2Labels = raw11265step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11265step1 raw11265step1Labels permutation8 permutation7
    mixedMoment B raw11265step2 raw11265step2Labels = mixedMoment B raw11265step3 raw11265step3Labels := by
      have ha : raw11265step3 = -raw11265step2 := by apply Matrix.ext; change ∀ i j, raw11265step3 i j = -(raw11265step2 i j); unfold raw11265step3 raw11265step2; decide +kernel
      have hl : raw11265step3Labels = raw11265step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11265step3 raw11265step3Labels = mixedMoment B raw11265step4 raw11265step4Labels := by
      have ha : raw11265step4 = raw11265step3 := by apply Matrix.ext; unfold raw11265step4 raw11265step3; decide +kernel
      have hl : raw11265step3Labels = labelEmbedding1 ∘ raw11265step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11265step3 raw11265step3Labels raw11265step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw11266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11266Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11266step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11266step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11266step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11266step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11266step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11266 raw11266Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw11266 raw11266Labels = mixedMoment B raw11266step0 raw11266step0Labels := by
      have hz : ∀ j, raw11266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11266step0 = (fun i j => raw11266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11266step0 raw11266; decide +kernel
      have hl : raw11266step0Labels = raw11266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11266 raw11266Labels permutation434 hz
    mixedMoment B raw11266step0 raw11266step0Labels = mixedMoment B raw11266step1 raw11266step1Labels := by
      have ha : raw11266step1 = (fun i j => raw11266step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11266step1 raw11266step0; decide +kernel
      have hl : raw11266step1Labels = raw11266step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11266step0 raw11266step0Labels permutation44 permutation7
    mixedMoment B raw11266step1 raw11266step1Labels = mixedMoment B raw11266step2 raw11266step2Labels := by
      have ha : raw11266step2 = -raw11266step1 := by apply Matrix.ext; change ∀ i j, raw11266step2 i j = -(raw11266step1 i j); unfold raw11266step2 raw11266step1; decide +kernel
      have hl : raw11266step2Labels = raw11266step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11266step2 raw11266step2Labels = mixedMoment B raw11266step3 raw11266step3Labels := by
      have ha : raw11266step3 = raw11266step2 := by apply Matrix.ext; unfold raw11266step3 raw11266step2; decide +kernel
      have hl : raw11266step2Labels = labelEmbedding1 ∘ raw11266step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11266step2 raw11266step2Labels raw11266step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw11267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11267Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11267step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11267step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11267step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11267step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11267step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11267 raw11267Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw11267 raw11267Labels = mixedMoment B raw11267step0 raw11267step0Labels := by
      have hz : ∀ j, raw11267 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11267step0 = (fun i j => raw11267 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11267step0 raw11267; decide +kernel
      have hl : raw11267step0Labels = raw11267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11267 raw11267Labels permutation434 hz
    mixedMoment B raw11267step0 raw11267step0Labels = mixedMoment B raw11267step1 raw11267step1Labels := by
      have ha : raw11267step1 = (fun i j => raw11267step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11267step1 raw11267step0; decide +kernel
      have hl : raw11267step1Labels = raw11267step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11267step0 raw11267step0Labels permutation46 permutation7
    mixedMoment B raw11267step1 raw11267step1Labels = mixedMoment B raw11267step2 raw11267step2Labels := by
      have ha : raw11267step2 = -raw11267step1 := by apply Matrix.ext; change ∀ i j, raw11267step2 i j = -(raw11267step1 i j); unfold raw11267step2 raw11267step1; decide +kernel
      have hl : raw11267step2Labels = raw11267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11267step2 raw11267step2Labels = mixedMoment B raw11267step3 raw11267step3Labels := by
      have ha : raw11267step3 = raw11267step2 := by apply Matrix.ext; unfold raw11267step3 raw11267step2; decide +kernel
      have hl : raw11267step2Labels = labelEmbedding1 ∘ raw11267step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11267step2 raw11267step2Labels raw11267step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw11268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11268Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11268step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11268step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11268step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11268step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11268 raw11268Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw11268 raw11268Labels = mixedMoment B raw11268step0 raw11268step0Labels := by
      have hz : ∀ j, raw11268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11268step0 = (fun i j => raw11268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11268step0 raw11268; decide +kernel
      have hl : raw11268step0Labels = raw11268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11268 raw11268Labels permutation434 hz
    mixedMoment B raw11268step0 raw11268step0Labels = mixedMoment B raw11268step1 raw11268step1Labels := by
      have ha : raw11268step1 = (fun i j => raw11268step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11268step1 raw11268step0; decide +kernel
      have hl : raw11268step1Labels = raw11268step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11268step0 raw11268step0Labels permutation46 permutation7
    mixedMoment B raw11268step1 raw11268step1Labels = mixedMoment B raw11268step2 raw11268step2Labels := by
      have ha : raw11268step2 = -raw11268step1 := by apply Matrix.ext; change ∀ i j, raw11268step2 i j = -(raw11268step1 i j); unfold raw11268step2 raw11268step1; decide +kernel
      have hl : raw11268step2Labels = raw11268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11268step2 raw11268step2Labels = mixedMoment B raw11268step3 raw11268step3Labels := by
      have ha : raw11268step3 = raw11268step2 := by apply Matrix.ext; unfold raw11268step3 raw11268step2; decide +kernel
      have hl : raw11268step2Labels = labelEmbedding1 ∘ raw11268step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11268step2 raw11268step2Labels raw11268step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw11269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11269Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11269step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11269step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11269step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11269step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11269 raw11269Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw11269 raw11269Labels = mixedMoment B raw11269step0 raw11269step0Labels := by
      have ha : raw11269step0 = (fun i j => raw11269 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11269step0 raw11269; decide +kernel
      have hl : raw11269step0Labels = raw11269Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11269 raw11269Labels permutation214 permutation7
    mixedMoment B raw11269step0 raw11269step0Labels = mixedMoment B raw11269step1 raw11269step1Labels := by
      have ha : raw11269step1 = -raw11269step0 := by apply Matrix.ext; change ∀ i j, raw11269step1 i j = -(raw11269step0 i j); unfold raw11269step1 raw11269step0; decide +kernel
      have hl : raw11269step1Labels = raw11269step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11269step1 raw11269step1Labels = mixedMoment B raw11269step2 raw11269step2Labels := by
      have ha : raw11269step2 = raw11269step1 := by apply Matrix.ext; unfold raw11269step2 raw11269step1; decide +kernel
      have hl : raw11269step1Labels = labelEmbedding1 ∘ raw11269step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11269step1 raw11269step1Labels raw11269step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw11270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11270step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11270step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11270step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11270step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11270step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11270step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11270step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11270 raw11270Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw11270 raw11270Labels = mixedMoment B raw11270step0 raw11270step0Labels := by
      have hz : ∀ j, raw11270 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11270step0 = (fun i j => raw11270 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11270step0 raw11270; decide +kernel
      have hl : raw11270step0Labels = raw11270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11270 raw11270Labels permutation520 hz
    mixedMoment B raw11270step0 raw11270step0Labels = mixedMoment B raw11270step1 raw11270step1Labels := by
      have hz : ∀ j, raw11270step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11270step1 = (fun i j => raw11270step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11270step1 raw11270step0; decide +kernel
      have hl : raw11270step1Labels = raw11270step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11270step0 raw11270step0Labels permutation104 hz
    mixedMoment B raw11270step1 raw11270step1Labels = mixedMoment B raw11270step2 raw11270step2Labels := by
      have ha : raw11270step2 = (fun i j => raw11270step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11270step2 raw11270step1; decide +kernel
      have hl : raw11270step2Labels = raw11270step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11270step1 raw11270step1Labels permutation10 permutation7
    mixedMoment B raw11270step2 raw11270step2Labels = mixedMoment B raw11270step3 raw11270step3Labels := by
      have ha : raw11270step3 = -raw11270step2 := by apply Matrix.ext; change ∀ i j, raw11270step3 i j = -(raw11270step2 i j); unfold raw11270step3 raw11270step2; decide +kernel
      have hl : raw11270step3Labels = raw11270step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11270step3 raw11270step3Labels = mixedMoment B raw11270step4 raw11270step4Labels := by
      have ha : raw11270step4 = raw11270step3 := by apply Matrix.ext; unfold raw11270step4 raw11270step3; decide +kernel
      have hl : raw11270step3Labels = labelEmbedding1 ∘ raw11270step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11270step3 raw11270step3Labels raw11270step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw11271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11271Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11271step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11271step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11271step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11271step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11271 raw11271Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw11271 raw11271Labels = mixedMoment B raw11271step0 raw11271step0Labels := by
      have hz : ∀ j, raw11271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11271step0 = (fun i j => raw11271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11271step0 raw11271; decide +kernel
      have hl : raw11271step0Labels = raw11271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11271 raw11271Labels permutation434 hz
    mixedMoment B raw11271step0 raw11271step0Labels = mixedMoment B raw11271step1 raw11271step1Labels := by
      have ha : raw11271step1 = (fun i j => raw11271step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11271step1 raw11271step0; decide +kernel
      have hl : raw11271step1Labels = raw11271step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11271step0 raw11271step0Labels permutation46 permutation7
    mixedMoment B raw11271step1 raw11271step1Labels = mixedMoment B raw11271step2 raw11271step2Labels := by
      have ha : raw11271step2 = -raw11271step1 := by apply Matrix.ext; change ∀ i j, raw11271step2 i j = -(raw11271step1 i j); unfold raw11271step2 raw11271step1; decide +kernel
      have hl : raw11271step2Labels = raw11271step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11271step2 raw11271step2Labels = mixedMoment B raw11271step3 raw11271step3Labels := by
      have ha : raw11271step3 = raw11271step2 := by apply Matrix.ext; unfold raw11271step3 raw11271step2; decide +kernel
      have hl : raw11271step2Labels = labelEmbedding1 ∘ raw11271step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11271step2 raw11271step2Labels raw11271step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw11272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11272step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11272step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11272step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11272step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11272 raw11272Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw11272 raw11272Labels = mixedMoment B raw11272step0 raw11272step0Labels := by
      have hz : ∀ j, raw11272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11272step0 = (fun i j => raw11272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11272step0 raw11272; decide +kernel
      have hl : raw11272step0Labels = raw11272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11272 raw11272Labels permutation434 hz
    mixedMoment B raw11272step0 raw11272step0Labels = mixedMoment B raw11272step1 raw11272step1Labels := by
      have ha : raw11272step1 = (fun i j => raw11272step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11272step1 raw11272step0; decide +kernel
      have hl : raw11272step1Labels = raw11272step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11272step0 raw11272step0Labels permutation44 permutation7
    mixedMoment B raw11272step1 raw11272step1Labels = mixedMoment B raw11272step2 raw11272step2Labels := by
      have ha : raw11272step2 = -raw11272step1 := by apply Matrix.ext; change ∀ i j, raw11272step2 i j = -(raw11272step1 i j); unfold raw11272step2 raw11272step1; decide +kernel
      have hl : raw11272step2Labels = raw11272step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11272step2 raw11272step2Labels = mixedMoment B raw11272step3 raw11272step3Labels := by
      have ha : raw11272step3 = raw11272step2 := by apply Matrix.ext; unfold raw11272step3 raw11272step2; decide +kernel
      have hl : raw11272step2Labels = labelEmbedding1 ∘ raw11272step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11272step2 raw11272step2Labels raw11272step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw11273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11273Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11273step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11273step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11273step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11273 raw11273Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw11273 raw11273Labels = mixedMoment B raw11273step0 raw11273step0Labels := by
      have hz : ∀ j, raw11273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11273step0 = (fun i j => raw11273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11273step0 raw11273; decide +kernel
      have hl : raw11273step0Labels = raw11273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11273 raw11273Labels permutation434 hz
    mixedMoment B raw11273step0 raw11273step0Labels = mixedMoment B raw11273step1 raw11273step1Labels := by
      have ha : raw11273step1 = (fun i j => raw11273step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11273step1 raw11273step0; decide +kernel
      have hl : raw11273step1Labels = raw11273step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11273step0 raw11273step0Labels permutation44 permutation7
    mixedMoment B raw11273step1 raw11273step1Labels = mixedMoment B raw11273step2 raw11273step2Labels := by
      have ha : raw11273step2 = -raw11273step1 := by apply Matrix.ext; change ∀ i j, raw11273step2 i j = -(raw11273step1 i j); unfold raw11273step2 raw11273step1; decide +kernel
      have hl : raw11273step2Labels = raw11273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11273step2 raw11273step2Labels = mixedMoment B raw11273step3 raw11273step3Labels := by
      have ha : raw11273step3 = raw11273step2 := by apply Matrix.ext; unfold raw11273step3 raw11273step2; decide +kernel
      have hl : raw11273step2Labels = labelEmbedding1 ∘ raw11273step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11273step2 raw11273step2Labels raw11273step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw11274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11274Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11274step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11274step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11274step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11274 raw11274Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw11274 raw11274Labels = mixedMoment B raw11274step0 raw11274step0Labels := by
      have ha : raw11274step0 = (fun i j => raw11274 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11274step0 raw11274; decide +kernel
      have hl : raw11274step0Labels = raw11274Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11274 raw11274Labels permutation212 permutation7
    mixedMoment B raw11274step0 raw11274step0Labels = mixedMoment B raw11274step1 raw11274step1Labels := by
      have ha : raw11274step1 = -raw11274step0 := by apply Matrix.ext; change ∀ i j, raw11274step1 i j = -(raw11274step0 i j); unfold raw11274step1 raw11274step0; decide +kernel
      have hl : raw11274step1Labels = raw11274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11274step1 raw11274step1Labels = mixedMoment B raw11274step2 raw11274step2Labels := by
      have ha : raw11274step2 = raw11274step1 := by apply Matrix.ext; unfold raw11274step2 raw11274step1; decide +kernel
      have hl : raw11274step1Labels = labelEmbedding1 ∘ raw11274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11274step1 raw11274step1Labels raw11274step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw11275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11275Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11275step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11275step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11275step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11275step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11275step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11275step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11275step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11275step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11275 raw11275Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw11275 raw11275Labels = mixedMoment B raw11275step0 raw11275step0Labels := by
      have hz : ∀ j, raw11275 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11275step0 = (fun i j => raw11275 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11275step0 raw11275; decide +kernel
      have hl : raw11275step0Labels = raw11275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11275 raw11275Labels permutation520 hz
    mixedMoment B raw11275step0 raw11275step0Labels = mixedMoment B raw11275step1 raw11275step1Labels := by
      have hz : ∀ j, raw11275step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11275step1 = (fun i j => raw11275step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11275step1 raw11275step0; decide +kernel
      have hl : raw11275step1Labels = raw11275step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11275step0 raw11275step0Labels permutation104 hz
    mixedMoment B raw11275step1 raw11275step1Labels = mixedMoment B raw11275step2 raw11275step2Labels := by
      have ha : raw11275step2 = (fun i j => raw11275step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11275step2 raw11275step1; decide +kernel
      have hl : raw11275step2Labels = raw11275step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11275step1 raw11275step1Labels permutation8 permutation7
    mixedMoment B raw11275step2 raw11275step2Labels = mixedMoment B raw11275step3 raw11275step3Labels := by
      have ha : raw11275step3 = -raw11275step2 := by apply Matrix.ext; change ∀ i j, raw11275step3 i j = -(raw11275step2 i j); unfold raw11275step3 raw11275step2; decide +kernel
      have hl : raw11275step3Labels = raw11275step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11275step3 raw11275step3Labels = mixedMoment B raw11275step4 raw11275step4Labels := by
      have ha : raw11275step4 = raw11275step3 := by apply Matrix.ext; unfold raw11275step4 raw11275step3; decide +kernel
      have hl : raw11275step3Labels = labelEmbedding1 ∘ raw11275step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11275step3 raw11275step3Labels raw11275step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw11276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11276Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11276step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11276step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11276step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11276step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11276step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11276 raw11276Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw11276 raw11276Labels = mixedMoment B raw11276step0 raw11276step0Labels := by
      have hz : ∀ j, raw11276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11276step0 = (fun i j => raw11276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11276step0 raw11276; decide +kernel
      have hl : raw11276step0Labels = raw11276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11276 raw11276Labels permutation434 hz
    mixedMoment B raw11276step0 raw11276step0Labels = mixedMoment B raw11276step1 raw11276step1Labels := by
      have ha : raw11276step1 = (fun i j => raw11276step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11276step1 raw11276step0; decide +kernel
      have hl : raw11276step1Labels = raw11276step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11276step0 raw11276step0Labels permutation44 permutation7
    mixedMoment B raw11276step1 raw11276step1Labels = mixedMoment B raw11276step2 raw11276step2Labels := by
      have ha : raw11276step2 = -raw11276step1 := by apply Matrix.ext; change ∀ i j, raw11276step2 i j = -(raw11276step1 i j); unfold raw11276step2 raw11276step1; decide +kernel
      have hl : raw11276step2Labels = raw11276step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11276step2 raw11276step2Labels = mixedMoment B raw11276step3 raw11276step3Labels := by
      have ha : raw11276step3 = raw11276step2 := by apply Matrix.ext; unfold raw11276step3 raw11276step2; decide +kernel
      have hl : raw11276step2Labels = labelEmbedding1 ∘ raw11276step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11276step2 raw11276step2Labels raw11276step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw11277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11277Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11277step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11277step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11277step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11277 raw11277Labels = mixedMoment B node1705 node1705Labels := by
  calc
    mixedMoment B raw11277 raw11277Labels = mixedMoment B raw11277step0 raw11277step0Labels := by
      have ha : raw11277step0 = (fun i j => raw11277 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11277step0 raw11277; decide +kernel
      have hl : raw11277step0Labels = raw11277Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11277 raw11277Labels permutation212 permutation7
    mixedMoment B raw11277step0 raw11277step0Labels = mixedMoment B raw11277step1 raw11277step1Labels := by
      have ha : raw11277step1 = -raw11277step0 := by apply Matrix.ext; change ∀ i j, raw11277step1 i j = -(raw11277step0 i j); unfold raw11277step1 raw11277step0; decide +kernel
      have hl : raw11277step1Labels = raw11277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11277step1 raw11277step1Labels = mixedMoment B raw11277step2 raw11277step2Labels := by
      have ha : raw11277step2 = raw11277step1 := by apply Matrix.ext; unfold raw11277step2 raw11277step1; decide +kernel
      have hl : raw11277step1Labels = labelEmbedding1 ∘ raw11277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11277step1 raw11277step1Labels raw11277step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1705 node1705Labels := by rfl

def raw11278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11278step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11278step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11278 raw11278Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw11278 raw11278Labels = mixedMoment B raw11278step0 raw11278step0Labels := by
      have ha : raw11278step0 = (fun i j => raw11278 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11278step0 raw11278; decide +kernel
      have hl : raw11278step0Labels = raw11278Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11278 raw11278Labels permutation212 permutation7
    mixedMoment B raw11278step0 raw11278step0Labels = mixedMoment B raw11278step1 raw11278step1Labels := by
      have ha : raw11278step1 = -raw11278step0 := by apply Matrix.ext; change ∀ i j, raw11278step1 i j = -(raw11278step0 i j); unfold raw11278step1 raw11278step0; decide +kernel
      have hl : raw11278step1Labels = raw11278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11278step1 raw11278step1Labels = mixedMoment B raw11278step2 raw11278step2Labels := by
      have ha : raw11278step2 = raw11278step1 := by apply Matrix.ext; unfold raw11278step2 raw11278step1; decide +kernel
      have hl : raw11278step1Labels = labelEmbedding1 ∘ raw11278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11278step1 raw11278step1Labels raw11278step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw11279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11279Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11279step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11279step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11279step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11279step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11279 raw11279Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw11279 raw11279Labels = mixedMoment B raw11279step0 raw11279step0Labels := by
      have ha : raw11279step0 = (fun i j => raw11279 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11279step0 raw11279; decide +kernel
      have hl : raw11279step0Labels = raw11279Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11279 raw11279Labels permutation214 permutation7
    mixedMoment B raw11279step0 raw11279step0Labels = mixedMoment B raw11279step1 raw11279step1Labels := by
      have ha : raw11279step1 = -raw11279step0 := by apply Matrix.ext; change ∀ i j, raw11279step1 i j = -(raw11279step0 i j); unfold raw11279step1 raw11279step0; decide +kernel
      have hl : raw11279step1Labels = raw11279step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11279step1 raw11279step1Labels = mixedMoment B raw11279step2 raw11279step2Labels := by
      have ha : raw11279step2 = raw11279step1 := by apply Matrix.ext; unfold raw11279step2 raw11279step1; decide +kernel
      have hl : raw11279step1Labels = labelEmbedding1 ∘ raw11279step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11279step1 raw11279step1Labels raw11279step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw11280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11280step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11280step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11280step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11280step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11280 raw11280Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw11280 raw11280Labels = mixedMoment B raw11280step0 raw11280step0Labels := by
      have hz : ∀ j, raw11280 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11280step0 = (fun i j => raw11280 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11280step0 raw11280; decide +kernel
      have hl : raw11280step0Labels = raw11280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11280 raw11280Labels permutation520 hz
    mixedMoment B raw11280step0 raw11280step0Labels = mixedMoment B raw11280step1 raw11280step1Labels := by
      have ha : raw11280step1 = (fun i j => raw11280step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11280step1 raw11280step0; decide +kernel
      have hl : raw11280step1Labels = raw11280step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11280step0 raw11280step0Labels permutation44 permutation7
    mixedMoment B raw11280step1 raw11280step1Labels = mixedMoment B raw11280step2 raw11280step2Labels := by
      have ha : raw11280step2 = -raw11280step1 := by apply Matrix.ext; change ∀ i j, raw11280step2 i j = -(raw11280step1 i j); unfold raw11280step2 raw11280step1; decide +kernel
      have hl : raw11280step2Labels = raw11280step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11280step2 raw11280step2Labels = mixedMoment B raw11280step3 raw11280step3Labels := by
      have ha : raw11280step3 = raw11280step2 := by apply Matrix.ext; unfold raw11280step3 raw11280step2; decide +kernel
      have hl : raw11280step2Labels = labelEmbedding1 ∘ raw11280step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11280step2 raw11280step2Labels raw11280step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw11281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11281Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11281step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11281step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11281step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11281 raw11281Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw11281 raw11281Labels = mixedMoment B raw11281step0 raw11281step0Labels := by
      have ha : raw11281step0 = (fun i j => raw11281 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11281step0 raw11281; decide +kernel
      have hl : raw11281step0Labels = raw11281Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11281 raw11281Labels permutation212 permutation7
    mixedMoment B raw11281step0 raw11281step0Labels = mixedMoment B raw11281step1 raw11281step1Labels := by
      have ha : raw11281step1 = -raw11281step0 := by apply Matrix.ext; change ∀ i j, raw11281step1 i j = -(raw11281step0 i j); unfold raw11281step1 raw11281step0; decide +kernel
      have hl : raw11281step1Labels = raw11281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11281step1 raw11281step1Labels = mixedMoment B raw11281step2 raw11281step2Labels := by
      have ha : raw11281step2 = raw11281step1 := by apply Matrix.ext; unfold raw11281step2 raw11281step1; decide +kernel
      have hl : raw11281step1Labels = labelEmbedding1 ∘ raw11281step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11281step1 raw11281step1Labels raw11281step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw11282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11282step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11282step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11282step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11282step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11282 raw11282Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw11282 raw11282Labels = mixedMoment B raw11282step0 raw11282step0Labels := by
      have hz : ∀ j, raw11282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11282step0 = (fun i j => raw11282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11282step0 raw11282; decide +kernel
      have hl : raw11282step0Labels = raw11282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11282 raw11282Labels permutation434 hz
    mixedMoment B raw11282step0 raw11282step0Labels = mixedMoment B raw11282step1 raw11282step1Labels := by
      have ha : raw11282step1 = (fun i j => raw11282step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11282step1 raw11282step0; decide +kernel
      have hl : raw11282step1Labels = raw11282step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11282step0 raw11282step0Labels permutation44 permutation7
    mixedMoment B raw11282step1 raw11282step1Labels = mixedMoment B raw11282step2 raw11282step2Labels := by
      have ha : raw11282step2 = -raw11282step1 := by apply Matrix.ext; change ∀ i j, raw11282step2 i j = -(raw11282step1 i j); unfold raw11282step2 raw11282step1; decide +kernel
      have hl : raw11282step2Labels = raw11282step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11282step2 raw11282step2Labels = mixedMoment B raw11282step3 raw11282step3Labels := by
      have ha : raw11282step3 = raw11282step2 := by apply Matrix.ext; unfold raw11282step3 raw11282step2; decide +kernel
      have hl : raw11282step2Labels = labelEmbedding1 ∘ raw11282step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11282step2 raw11282step2Labels raw11282step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw11283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11283Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11283step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11283step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11283step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11283step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11283 raw11283Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw11283 raw11283Labels = mixedMoment B raw11283step0 raw11283step0Labels := by
      have hz : ∀ j, raw11283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11283step0 = (fun i j => raw11283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11283step0 raw11283; decide +kernel
      have hl : raw11283step0Labels = raw11283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11283 raw11283Labels permutation434 hz
    mixedMoment B raw11283step0 raw11283step0Labels = mixedMoment B raw11283step1 raw11283step1Labels := by
      have ha : raw11283step1 = (fun i j => raw11283step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11283step1 raw11283step0; decide +kernel
      have hl : raw11283step1Labels = raw11283step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11283step0 raw11283step0Labels permutation44 permutation7
    mixedMoment B raw11283step1 raw11283step1Labels = mixedMoment B raw11283step2 raw11283step2Labels := by
      have ha : raw11283step2 = -raw11283step1 := by apply Matrix.ext; change ∀ i j, raw11283step2 i j = -(raw11283step1 i j); unfold raw11283step2 raw11283step1; decide +kernel
      have hl : raw11283step2Labels = raw11283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11283step2 raw11283step2Labels = mixedMoment B raw11283step3 raw11283step3Labels := by
      have ha : raw11283step3 = raw11283step2 := by apply Matrix.ext; unfold raw11283step3 raw11283step2; decide +kernel
      have hl : raw11283step2Labels = labelEmbedding1 ∘ raw11283step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11283step2 raw11283step2Labels raw11283step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw11284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11284step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11284step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11284step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11284step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11284step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11284 raw11284Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw11284 raw11284Labels = mixedMoment B raw11284step0 raw11284step0Labels := by
      have hz : ∀ j, raw11284 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11284step0 = (fun i j => raw11284 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11284step0 raw11284; decide +kernel
      have hl : raw11284step0Labels = raw11284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11284 raw11284Labels permutation434 hz
    mixedMoment B raw11284step0 raw11284step0Labels = mixedMoment B raw11284step1 raw11284step1Labels := by
      have ha : raw11284step1 = (fun i j => raw11284step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11284step1 raw11284step0; decide +kernel
      have hl : raw11284step1Labels = raw11284step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11284step0 raw11284step0Labels permutation46 permutation7
    mixedMoment B raw11284step1 raw11284step1Labels = mixedMoment B raw11284step2 raw11284step2Labels := by
      have ha : raw11284step2 = -raw11284step1 := by apply Matrix.ext; change ∀ i j, raw11284step2 i j = -(raw11284step1 i j); unfold raw11284step2 raw11284step1; decide +kernel
      have hl : raw11284step2Labels = raw11284step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11284step2 raw11284step2Labels = mixedMoment B raw11284step3 raw11284step3Labels := by
      have ha : raw11284step3 = raw11284step2 := by apply Matrix.ext; unfold raw11284step3 raw11284step2; decide +kernel
      have hl : raw11284step2Labels = labelEmbedding1 ∘ raw11284step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11284step2 raw11284step2Labels raw11284step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw11285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11285Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11285step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11285step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11285step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11285 raw11285Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw11285 raw11285Labels = mixedMoment B raw11285step0 raw11285step0Labels := by
      have ha : raw11285step0 = (fun i j => raw11285 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11285step0 raw11285; decide +kernel
      have hl : raw11285step0Labels = raw11285Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11285 raw11285Labels permutation212 permutation7
    mixedMoment B raw11285step0 raw11285step0Labels = mixedMoment B raw11285step1 raw11285step1Labels := by
      have ha : raw11285step1 = -raw11285step0 := by apply Matrix.ext; change ∀ i j, raw11285step1 i j = -(raw11285step0 i j); unfold raw11285step1 raw11285step0; decide +kernel
      have hl : raw11285step1Labels = raw11285step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11285step1 raw11285step1Labels = mixedMoment B raw11285step2 raw11285step2Labels := by
      have ha : raw11285step2 = raw11285step1 := by apply Matrix.ext; unfold raw11285step2 raw11285step1; decide +kernel
      have hl : raw11285step1Labels = labelEmbedding1 ∘ raw11285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11285step1 raw11285step1Labels raw11285step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw11286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw11286step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11286step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11286step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11286step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11286step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11286 raw11286Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw11286 raw11286Labels = mixedMoment B raw11286step0 raw11286step0Labels := by
      have hz : ∀ j, raw11286 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11286step0 = (fun i j => raw11286 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11286step0 raw11286; decide +kernel
      have hl : raw11286step0Labels = raw11286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11286 raw11286Labels permutation434 hz
    mixedMoment B raw11286step0 raw11286step0Labels = mixedMoment B raw11286step1 raw11286step1Labels := by
      have ha : raw11286step1 = (fun i j => raw11286step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11286step1 raw11286step0; decide +kernel
      have hl : raw11286step1Labels = raw11286step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11286step0 raw11286step0Labels permutation44 permutation7
    mixedMoment B raw11286step1 raw11286step1Labels = mixedMoment B raw11286step2 raw11286step2Labels := by
      have ha : raw11286step2 = -raw11286step1 := by apply Matrix.ext; change ∀ i j, raw11286step2 i j = -(raw11286step1 i j); unfold raw11286step2 raw11286step1; decide +kernel
      have hl : raw11286step2Labels = raw11286step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11286step2 raw11286step2Labels = mixedMoment B raw11286step3 raw11286step3Labels := by
      have ha : raw11286step3 = raw11286step2 := by apply Matrix.ext; unfold raw11286step3 raw11286step2; decide +kernel
      have hl : raw11286step2Labels = labelEmbedding1 ∘ raw11286step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11286step2 raw11286step2Labels raw11286step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw11287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11287step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw11287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11287step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11287step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11287step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11287 raw11287Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw11287 raw11287Labels = mixedMoment B raw11287step0 raw11287step0Labels := by
      have hz : ∀ j, raw11287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11287step0 = (fun i j => raw11287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11287step0 raw11287; decide +kernel
      have hl : raw11287step0Labels = raw11287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11287 raw11287Labels permutation434 hz
    mixedMoment B raw11287step0 raw11287step0Labels = mixedMoment B raw11287step1 raw11287step1Labels := by
      have ha : raw11287step1 = (fun i j => raw11287step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11287step1 raw11287step0; decide +kernel
      have hl : raw11287step1Labels = raw11287step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11287step0 raw11287step0Labels permutation44 permutation7
    mixedMoment B raw11287step1 raw11287step1Labels = mixedMoment B raw11287step2 raw11287step2Labels := by
      have ha : raw11287step2 = -raw11287step1 := by apply Matrix.ext; change ∀ i j, raw11287step2 i j = -(raw11287step1 i j); unfold raw11287step2 raw11287step1; decide +kernel
      have hl : raw11287step2Labels = raw11287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11287step2 raw11287step2Labels = mixedMoment B raw11287step3 raw11287step3Labels := by
      have ha : raw11287step3 = raw11287step2 := by apply Matrix.ext; unfold raw11287step3 raw11287step2; decide +kernel
      have hl : raw11287step2Labels = labelEmbedding1 ∘ raw11287step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11287step2 raw11287step2Labels raw11287step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

def raw11288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw11288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw11288step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11288step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw11288step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11288 raw11288Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw11288 raw11288Labels = mixedMoment B raw11288step0 raw11288step0Labels := by
      have hz : ∀ j, raw11288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11288step0 = (fun i j => raw11288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11288step0 raw11288; decide +kernel
      have hl : raw11288step0Labels = raw11288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11288 raw11288Labels permutation434 hz
    mixedMoment B raw11288step0 raw11288step0Labels = mixedMoment B raw11288step1 raw11288step1Labels := by
      have ha : raw11288step1 = (fun i j => raw11288step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11288step1 raw11288step0; decide +kernel
      have hl : raw11288step1Labels = raw11288step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11288step0 raw11288step0Labels permutation44 permutation7
    mixedMoment B raw11288step1 raw11288step1Labels = mixedMoment B raw11288step2 raw11288step2Labels := by
      have ha : raw11288step2 = -raw11288step1 := by apply Matrix.ext; change ∀ i j, raw11288step2 i j = -(raw11288step1 i j); unfold raw11288step2 raw11288step1; decide +kernel
      have hl : raw11288step2Labels = raw11288step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11288step2 raw11288step2Labels = mixedMoment B raw11288step3 raw11288step3Labels := by
      have ha : raw11288step3 = raw11288step2 := by apply Matrix.ext; unfold raw11288step3 raw11288step2; decide +kernel
      have hl : raw11288step2Labels = labelEmbedding1 ∘ raw11288step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11288step2 raw11288step2Labels raw11288step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw11289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11289step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw11289step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw11289step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw11289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11289 raw11289Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw11289 raw11289Labels = mixedMoment B raw11289step0 raw11289step0Labels := by
      have hz : ∀ j, raw11289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11289step0 = (fun i j => raw11289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11289step0 raw11289; decide +kernel
      have hl : raw11289step0Labels = raw11289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11289 raw11289Labels permutation434 hz
    mixedMoment B raw11289step0 raw11289step0Labels = mixedMoment B raw11289step1 raw11289step1Labels := by
      have ha : raw11289step1 = (fun i j => raw11289step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11289step1 raw11289step0; decide +kernel
      have hl : raw11289step1Labels = raw11289step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11289step0 raw11289step0Labels permutation46 permutation7
    mixedMoment B raw11289step1 raw11289step1Labels = mixedMoment B raw11289step2 raw11289step2Labels := by
      have ha : raw11289step2 = -raw11289step1 := by apply Matrix.ext; change ∀ i j, raw11289step2 i j = -(raw11289step1 i j); unfold raw11289step2 raw11289step1; decide +kernel
      have hl : raw11289step2Labels = raw11289step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11289step2 raw11289step2Labels = mixedMoment B raw11289step3 raw11289step3Labels := by
      have ha : raw11289step3 = raw11289step2 := by apply Matrix.ext; unfold raw11289step3 raw11289step2; decide +kernel
      have hl : raw11289step2Labels = labelEmbedding1 ∘ raw11289step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11289step2 raw11289step2Labels raw11289step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw11290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw11290step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11290 raw11290Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw11290 raw11290Labels = mixedMoment B raw11290step0 raw11290step0Labels := by
      have ha : raw11290step0 = (fun i j => raw11290 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11290step0 raw11290; decide +kernel
      have hl : raw11290step0Labels = raw11290Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11290 raw11290Labels permutation212 permutation7
    mixedMoment B raw11290step0 raw11290step0Labels = mixedMoment B raw11290step1 raw11290step1Labels := by
      have ha : raw11290step1 = -raw11290step0 := by apply Matrix.ext; change ∀ i j, raw11290step1 i j = -(raw11290step0 i j); unfold raw11290step1 raw11290step0; decide +kernel
      have hl : raw11290step1Labels = raw11290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11290step1 raw11290step1Labels = mixedMoment B raw11290step2 raw11290step2Labels := by
      have ha : raw11290step2 = raw11290step1 := by apply Matrix.ext; unfold raw11290step2 raw11290step1; decide +kernel
      have hl : raw11290step1Labels = labelEmbedding1 ∘ raw11290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11290step1 raw11290step1Labels raw11290step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw11291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw11291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw11291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11291step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11291step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11291step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw11291step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11291step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11291step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11291step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11291step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11291 raw11291Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw11291 raw11291Labels = mixedMoment B raw11291step0 raw11291step0Labels := by
      have hz : ∀ j, raw11291 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11291step0 = (fun i j => raw11291 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11291step0 raw11291; decide +kernel
      have hl : raw11291step0Labels = raw11291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11291 raw11291Labels permutation520 hz
    mixedMoment B raw11291step0 raw11291step0Labels = mixedMoment B raw11291step1 raw11291step1Labels := by
      have hz : ∀ j, raw11291step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11291step1 = (fun i j => raw11291step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11291step1 raw11291step0; decide +kernel
      have hl : raw11291step1Labels = raw11291step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11291step0 raw11291step0Labels permutation104 hz
    mixedMoment B raw11291step1 raw11291step1Labels = mixedMoment B raw11291step2 raw11291step2Labels := by
      have ha : raw11291step2 = (fun i j => raw11291step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11291step2 raw11291step1; decide +kernel
      have hl : raw11291step2Labels = raw11291step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11291step1 raw11291step1Labels permutation8 permutation7
    mixedMoment B raw11291step2 raw11291step2Labels = mixedMoment B raw11291step3 raw11291step3Labels := by
      have ha : raw11291step3 = -raw11291step2 := by apply Matrix.ext; change ∀ i j, raw11291step3 i j = -(raw11291step2 i j); unfold raw11291step3 raw11291step2; decide +kernel
      have hl : raw11291step3Labels = raw11291step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11291step3 raw11291step3Labels = mixedMoment B raw11291step4 raw11291step4Labels := by
      have ha : raw11291step4 = raw11291step3 := by apply Matrix.ext; unfold raw11291step4 raw11291step3; decide +kernel
      have hl : raw11291step3Labels = labelEmbedding1 ∘ raw11291step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11291step3 raw11291step3Labels raw11291step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw11292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11292Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11292step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11292 raw11292Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw11292 raw11292Labels = mixedMoment B raw11292step0 raw11292step0Labels := by
      have hz : ∀ j, raw11292 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11292step0 = (fun i j => raw11292 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11292step0 raw11292; decide +kernel
      have hl : raw11292step0Labels = raw11292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11292 raw11292Labels permutation434 hz
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw11293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11293Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11293step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11293 raw11293Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw11293 raw11293Labels = mixedMoment B raw11293step0 raw11293step0Labels := by
      have hz : ∀ j, raw11293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11293step0 = (fun i j => raw11293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11293step0 raw11293; decide +kernel
      have hl : raw11293step0Labels = raw11293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11293 raw11293Labels permutation434 hz
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw11294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11294Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11294 raw11294Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw11294 raw11294Labels = mixedMoment B raw11294step0 raw11294step0Labels := by
      have hz : ∀ j, raw11294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11294step0 = (fun i j => raw11294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11294step0 raw11294; decide +kernel
      have hl : raw11294step0Labels = raw11294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11294 raw11294Labels permutation434 hz
    mixedMoment B raw11294step0 raw11294step0Labels = mixedMoment B raw11294step1 raw11294step1Labels := by
      have ha : raw11294step1 = (fun i j => raw11294step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11294step1 raw11294step0; decide +kernel
      have hl : raw11294step1Labels = raw11294step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11294step0 raw11294step0Labels permutation38 permutation2
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw11295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11295Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11295step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11295 raw11295Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw11295 raw11295Labels = mixedMoment B raw11295step0 raw11295step0Labels := by
      have ha : raw11295step0 = (fun i j => raw11295 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11295step0 raw11295; decide +kernel
      have hl : raw11295step0Labels = raw11295Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11295 raw11295Labels permutation200 permutation2
    _ = mixedMoment B node3525 node3525Labels := by rfl

def raw11296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11296Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11296 raw11296Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw11296 raw11296Labels = mixedMoment B raw11296step0 raw11296step0Labels := by
      have hz : ∀ j, raw11296 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11296step0 = (fun i j => raw11296 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11296step0 raw11296; decide +kernel
      have hl : raw11296step0Labels = raw11296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11296 raw11296Labels permutation520 hz
    mixedMoment B raw11296step0 raw11296step0Labels = mixedMoment B raw11296step1 raw11296step1Labels := by
      have hz : ∀ j, raw11296step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11296step1 = (fun i j => raw11296step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11296step1 raw11296step0; decide +kernel
      have hl : raw11296step1Labels = raw11296step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11296step0 raw11296step0Labels permutation104 hz
    _ = mixedMoment B node3623 node3623Labels := by rfl

def raw11297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11297Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11297 raw11297Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw11297 raw11297Labels = mixedMoment B raw11297step0 raw11297step0Labels := by
      have hz : ∀ j, raw11297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11297step0 = (fun i j => raw11297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11297step0 raw11297; decide +kernel
      have hl : raw11297step0Labels = raw11297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11297 raw11297Labels permutation434 hz
    _ = mixedMoment B node3622 node3622Labels := by rfl

def raw11298 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]
def raw11298Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11298step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw11298step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11298step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11298step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11298 raw11298Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11298 raw11298Labels = mixedMoment B raw11298step0 raw11298step0Labels := by
      have hz : ∀ j, raw11298 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11298step0 = (fun i j => raw11298 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11298step0 raw11298; decide +kernel
      have hl : raw11298step0Labels = raw11298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11298 raw11298Labels permutation520 hz
    mixedMoment B raw11298step0 raw11298step0Labels = mixedMoment B raw11298step1 raw11298step1Labels := by
      have hz : ∀ j, raw11298step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11298step1 = (fun i j => raw11298step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11298step1 raw11298step0; decide +kernel
      have hl : raw11298step1Labels = raw11298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11298step0 raw11298step0Labels permutation104 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw11299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11299 raw11299Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw11299 raw11299Labels = mixedMoment B raw11299step0 raw11299step0Labels := by
      have hz : ∀ j, raw11299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11299step0 = (fun i j => raw11299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11299step0 raw11299; decide +kernel
      have hl : raw11299step0Labels = raw11299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11299 raw11299Labels permutation434 hz
    mixedMoment B raw11299step0 raw11299step0Labels = mixedMoment B raw11299step1 raw11299step1Labels := by
      have ha : raw11299step1 = (fun i j => raw11299step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11299step1 raw11299step0; decide +kernel
      have hl : raw11299step1Labels = raw11299step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11299step0 raw11299step0Labels permutation40 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw11300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11300 raw11300Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw11300 raw11300Labels = mixedMoment B raw11300step0 raw11300step0Labels := by
      have hz : ∀ j, raw11300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11300step0 = (fun i j => raw11300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11300step0 raw11300; decide +kernel
      have hl : raw11300step0Labels = raw11300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11300 raw11300Labels permutation434 hz
    mixedMoment B raw11300step0 raw11300step0Labels = mixedMoment B raw11300step1 raw11300step1Labels := by
      have ha : raw11300step1 = (fun i j => raw11300step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11300step1 raw11300step0; decide +kernel
      have hl : raw11300step1Labels = raw11300step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11300step0 raw11300step0Labels permutation34 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw11301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11301 raw11301Labels = mixedMoment B node1020 node1020Labels := by
  calc
    _ = mixedMoment B node1020 node1020Labels := by rfl

def raw11302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11302 raw11302Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw11302 raw11302Labels = mixedMoment B raw11302step0 raw11302step0Labels := by
      have hz : ∀ j, raw11302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11302step0 = (fun i j => raw11302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11302step0 raw11302; decide +kernel
      have hl : raw11302step0Labels = raw11302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11302 raw11302Labels permutation434 hz
    _ = mixedMoment B node1026 node1026Labels := by rfl

def raw11303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11303 raw11303Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw11303 raw11303Labels = mixedMoment B raw11303step0 raw11303step0Labels := by
      have hz : ∀ j, raw11303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11303step0 = (fun i j => raw11303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11303step0 raw11303; decide +kernel
      have hl : raw11303step0Labels = raw11303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11303 raw11303Labels permutation434 hz
    _ = mixedMoment B node1022 node1022Labels := by rfl

def raw11304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11304step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11304 raw11304Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw11304 raw11304Labels = mixedMoment B raw11304step0 raw11304step0Labels := by
      have hz : ∀ j, raw11304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11304step0 = (fun i j => raw11304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11304step0 raw11304; decide +kernel
      have hl : raw11304step0Labels = raw11304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11304 raw11304Labels permutation434 hz
    mixedMoment B raw11304step0 raw11304step0Labels = mixedMoment B raw11304step1 raw11304step1Labels := by
      have ha : raw11304step1 = (fun i j => raw11304step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11304step1 raw11304step0; decide +kernel
      have hl : raw11304step1Labels = raw11304step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11304step0 raw11304step0Labels permutation40 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw11305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11305 raw11305Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw11305 raw11305Labels = mixedMoment B raw11305step0 raw11305step0Labels := by
      have ha : raw11305step0 = (fun i j => raw11305 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11305step0 raw11305; decide +kernel
      have hl : raw11305step0Labels = raw11305Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11305 raw11305Labels permutation208 permutation2
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw11306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11306step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11306step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11306 raw11306Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw11306 raw11306Labels = mixedMoment B raw11306step0 raw11306step0Labels := by
      have hz : ∀ j, raw11306 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11306step0 = (fun i j => raw11306 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11306step0 raw11306; decide +kernel
      have hl : raw11306step0Labels = raw11306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11306 raw11306Labels permutation520 hz
    mixedMoment B raw11306step0 raw11306step0Labels = mixedMoment B raw11306step1 raw11306step1Labels := by
      have hz : ∀ j, raw11306step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11306step1 = (fun i j => raw11306step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11306step1 raw11306step0; decide +kernel
      have hl : raw11306step1Labels = raw11306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11306step0 raw11306step0Labels permutation104 hz
    mixedMoment B raw11306step1 raw11306step1Labels = mixedMoment B raw11306step2 raw11306step2Labels := by
      have ha : raw11306step2 = (fun i j => raw11306step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11306step2 raw11306step1; decide +kernel
      have hl : raw11306step2Labels = raw11306step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11306step1 raw11306step1Labels permutation10 permutation2
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw11307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11307 raw11307Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw11307 raw11307Labels = mixedMoment B raw11307step0 raw11307step0Labels := by
      have hz : ∀ j, raw11307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11307step0 = (fun i j => raw11307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11307step0 raw11307; decide +kernel
      have hl : raw11307step0Labels = raw11307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11307 raw11307Labels permutation434 hz
    mixedMoment B raw11307step0 raw11307step0Labels = mixedMoment B raw11307step1 raw11307step1Labels := by
      have ha : raw11307step1 = (fun i j => raw11307step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11307step1 raw11307step0; decide +kernel
      have hl : raw11307step1Labels = raw11307step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11307step0 raw11307step0Labels permutation40 permutation2
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw11308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11308 raw11308Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw11308 raw11308Labels = mixedMoment B raw11308step0 raw11308step0Labels := by
      have hz : ∀ j, raw11308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11308step0 = (fun i j => raw11308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11308step0 raw11308; decide +kernel
      have hl : raw11308step0Labels = raw11308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11308 raw11308Labels permutation434 hz
    mixedMoment B raw11308step0 raw11308step0Labels = mixedMoment B raw11308step1 raw11308step1Labels := by
      have ha : raw11308step1 = (fun i j => raw11308step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11308step1 raw11308step0; decide +kernel
      have hl : raw11308step1Labels = raw11308step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11308step0 raw11308step0Labels permutation34 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw11309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11309 raw11309Labels = mixedMoment B node2088 node2088Labels := by
  calc
    _ = mixedMoment B node2088 node2088Labels := by rfl

def raw11310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11310 raw11310Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw11310 raw11310Labels = mixedMoment B raw11310step0 raw11310step0Labels := by
      have hz : ∀ j, raw11310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11310step0 = (fun i j => raw11310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11310step0 raw11310; decide +kernel
      have hl : raw11310step0Labels = raw11310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11310 raw11310Labels permutation434 hz
    _ = mixedMoment B node2094 node2094Labels := by rfl

def raw11311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11311 raw11311Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw11311 raw11311Labels = mixedMoment B raw11311step0 raw11311step0Labels := by
      have hz : ∀ j, raw11311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11311step0 = (fun i j => raw11311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11311step0 raw11311; decide +kernel
      have hl : raw11311step0Labels = raw11311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11311 raw11311Labels permutation434 hz
    _ = mixedMoment B node2090 node2090Labels := by rfl

def raw11312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11312 raw11312Labels = mixedMoment B node2088 node2088Labels := by
  calc
    mixedMoment B raw11312 raw11312Labels = mixedMoment B raw11312step0 raw11312step0Labels := by
      have ha : raw11312step0 = (fun i j => raw11312 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11312step0 raw11312; decide +kernel
      have hl : raw11312step0Labels = raw11312Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11312 raw11312Labels permutation176 permutation2
    _ = mixedMoment B node2088 node2088Labels := by rfl

def raw11313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11313 raw11313Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw11313 raw11313Labels = mixedMoment B raw11313step0 raw11313step0Labels := by
      have hz : ∀ j, raw11313 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11313step0 = (fun i j => raw11313 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11313step0 raw11313; decide +kernel
      have hl : raw11313step0Labels = raw11313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11313 raw11313Labels permutation520 hz
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw11314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11314 raw11314Labels = mixedMoment B node2243 node2243Labels := by
  calc
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw11315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11315step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11315step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11315 raw11315Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw11315 raw11315Labels = mixedMoment B raw11315step0 raw11315step0Labels := by
      have hz : ∀ j, raw11315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11315step0 = (fun i j => raw11315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11315step0 raw11315; decide +kernel
      have hl : raw11315step0Labels = raw11315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11315 raw11315Labels permutation434 hz
    mixedMoment B raw11315step0 raw11315step0Labels = mixedMoment B raw11315step1 raw11315step1Labels := by
      have ha : raw11315step1 = (fun i j => raw11315step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11315step1 raw11315step0; decide +kernel
      have hl : raw11315step1Labels = raw11315step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11315step0 raw11315step0Labels permutation32 permutation3
    mixedMoment B raw11315step1 raw11315step1Labels = mixedMoment B raw11315step2 raw11315step2Labels := by
      have ha : raw11315step2 = raw11315step1 := by apply Matrix.ext; unfold raw11315step2 raw11315step1; decide +kernel
      have hl : raw11315step1Labels = labelEmbedding6 ∘ raw11315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11315step1 raw11315step1Labels raw11315step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw11316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11316step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11316 raw11316Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw11316 raw11316Labels = mixedMoment B raw11316step0 raw11316step0Labels := by
      have hz : ∀ j, raw11316 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11316step0 = (fun i j => raw11316 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11316step0 raw11316; decide +kernel
      have hl : raw11316step0Labels = raw11316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11316 raw11316Labels permutation434 hz
    mixedMoment B raw11316step0 raw11316step0Labels = mixedMoment B raw11316step1 raw11316step1Labels := by
      have ha : raw11316step1 = (fun i j => raw11316step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11316step1 raw11316step0; decide +kernel
      have hl : raw11316step1Labels = raw11316step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11316step0 raw11316step0Labels permutation38 permutation3
    mixedMoment B raw11316step1 raw11316step1Labels = mixedMoment B raw11316step2 raw11316step2Labels := by
      have ha : raw11316step2 = raw11316step1 := by apply Matrix.ext; unfold raw11316step2 raw11316step1; decide +kernel
      have hl : raw11316step1Labels = labelEmbedding6 ∘ raw11316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11316step1 raw11316step1Labels raw11316step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw11317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11317step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11317 raw11317Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw11317 raw11317Labels = mixedMoment B raw11317step0 raw11317step0Labels := by
      have ha : raw11317step0 = (fun i j => raw11317 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11317step0 raw11317; decide +kernel
      have hl : raw11317step0Labels = raw11317Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11317 raw11317Labels permutation200 permutation3
    mixedMoment B raw11317step0 raw11317step0Labels = mixedMoment B raw11317step1 raw11317step1Labels := by
      have ha : raw11317step1 = raw11317step0 := by apply Matrix.ext; unfold raw11317step1 raw11317step0; decide +kernel
      have hl : raw11317step0Labels = labelEmbedding6 ∘ raw11317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11317step0 raw11317step0Labels raw11317step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw11318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw11318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11318step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11318step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11318step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11318step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11318 raw11318Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw11318 raw11318Labels = mixedMoment B raw11318step0 raw11318step0Labels := by
      have hz : ∀ j, raw11318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11318step0 = (fun i j => raw11318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11318step0 raw11318; decide +kernel
      have hl : raw11318step0Labels = raw11318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11318 raw11318Labels permutation434 hz
    mixedMoment B raw11318step0 raw11318step0Labels = mixedMoment B raw11318step1 raw11318step1Labels := by
      have ha : raw11318step1 = (fun i j => raw11318step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11318step1 raw11318step0; decide +kernel
      have hl : raw11318step1Labels = raw11318step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11318step0 raw11318step0Labels permutation44 permutation5
    mixedMoment B raw11318step1 raw11318step1Labels = mixedMoment B raw11318step2 raw11318step2Labels := by
      have ha : raw11318step2 = -raw11318step1 := by apply Matrix.ext; change ∀ i j, raw11318step2 i j = -(raw11318step1 i j); unfold raw11318step2 raw11318step1; decide +kernel
      have hl : raw11318step2Labels = raw11318step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11318step2 raw11318step2Labels = mixedMoment B raw11318step3 raw11318step3Labels := by
      have ha : raw11318step3 = raw11318step2 := by apply Matrix.ext; unfold raw11318step3 raw11318step2; decide +kernel
      have hl : raw11318step2Labels = labelEmbedding8 ∘ raw11318step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11318step2 raw11318step2Labels raw11318step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw11319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw11319step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw11319step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11319 raw11319Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw11319 raw11319Labels = mixedMoment B raw11319step0 raw11319step0Labels := by
      have hz : ∀ j, raw11319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11319step0 = (fun i j => raw11319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11319step0 raw11319; decide +kernel
      have hl : raw11319step0Labels = raw11319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11319 raw11319Labels permutation434 hz
    mixedMoment B raw11319step0 raw11319step0Labels = mixedMoment B raw11319step1 raw11319step1Labels := by
      have ha : raw11319step1 = (fun i j => raw11319step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11319step1 raw11319step0; decide +kernel
      have hl : raw11319step1Labels = raw11319step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11319step0 raw11319step0Labels permutation32 permutation3
    mixedMoment B raw11319step1 raw11319step1Labels = mixedMoment B raw11319step2 raw11319step2Labels := by
      have ha : raw11319step2 = raw11319step1 := by apply Matrix.ext; unfold raw11319step2 raw11319step1; decide +kernel
      have hl : raw11319step1Labels = labelEmbedding6 ∘ raw11319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11319step1 raw11319step1Labels raw11319step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw11320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11320step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11320step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11320 raw11320Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw11320 raw11320Labels = mixedMoment B raw11320step0 raw11320step0Labels := by
      have hz : ∀ j, raw11320 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11320step0 = (fun i j => raw11320 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11320step0 raw11320; decide +kernel
      have hl : raw11320step0Labels = raw11320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11320 raw11320Labels permutation434 hz
    mixedMoment B raw11320step0 raw11320step0Labels = mixedMoment B raw11320step1 raw11320step1Labels := by
      have ha : raw11320step1 = (fun i j => raw11320step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11320step1 raw11320step0; decide +kernel
      have hl : raw11320step1Labels = raw11320step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11320step0 raw11320step0Labels permutation40 permutation3
    mixedMoment B raw11320step1 raw11320step1Labels = mixedMoment B raw11320step2 raw11320step2Labels := by
      have ha : raw11320step2 = raw11320step1 := by apply Matrix.ext; unfold raw11320step2 raw11320step1; decide +kernel
      have hl : raw11320step1Labels = labelEmbedding6 ∘ raw11320step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11320step1 raw11320step1Labels raw11320step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

def raw11321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11321step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11321step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11321 raw11321Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11321 raw11321Labels = mixedMoment B raw11321step0 raw11321step0Labels := by
      have hz : ∀ j, raw11321 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11321step0 = (fun i j => raw11321 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11321step0 raw11321; decide +kernel
      have hl : raw11321step0Labels = raw11321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11321 raw11321Labels permutation434 hz
    mixedMoment B raw11321step0 raw11321step0Labels = mixedMoment B raw11321step1 raw11321step1Labels := by
      have ha : raw11321step1 = (fun i j => raw11321step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11321step1 raw11321step0; decide +kernel
      have hl : raw11321step1Labels = raw11321step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11321step0 raw11321step0Labels permutation40 permutation3
    mixedMoment B raw11321step1 raw11321step1Labels = mixedMoment B raw11321step2 raw11321step2Labels := by
      have ha : raw11321step2 = raw11321step1 := by apply Matrix.ext; unfold raw11321step2 raw11321step1; decide +kernel
      have hl : raw11321step1Labels = labelEmbedding6 ∘ raw11321step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11321step1 raw11321step1Labels raw11321step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw11322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11322step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11322 raw11322Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw11322 raw11322Labels = mixedMoment B raw11322step0 raw11322step0Labels := by
      have ha : raw11322step0 = (fun i j => raw11322 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11322step0 raw11322; decide +kernel
      have hl : raw11322step0Labels = raw11322Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11322 raw11322Labels permutation208 permutation3
    mixedMoment B raw11322step0 raw11322step0Labels = mixedMoment B raw11322step1 raw11322step1Labels := by
      have ha : raw11322step1 = raw11322step0 := by apply Matrix.ext; unfold raw11322step1 raw11322step0; decide +kernel
      have hl : raw11322step0Labels = labelEmbedding6 ∘ raw11322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11322step0 raw11322step0Labels raw11322step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

def raw11323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw11323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw11323step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11323step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11323step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11323step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11323 raw11323Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11323 raw11323Labels = mixedMoment B raw11323step0 raw11323step0Labels := by
      have hz : ∀ j, raw11323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11323step0 = (fun i j => raw11323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11323step0 raw11323; decide +kernel
      have hl : raw11323step0Labels = raw11323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11323 raw11323Labels permutation434 hz
    mixedMoment B raw11323step0 raw11323step0Labels = mixedMoment B raw11323step1 raw11323step1Labels := by
      have ha : raw11323step1 = (fun i j => raw11323step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11323step1 raw11323step0; decide +kernel
      have hl : raw11323step1Labels = raw11323step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11323step0 raw11323step0Labels permutation47 permutation5
    mixedMoment B raw11323step1 raw11323step1Labels = mixedMoment B raw11323step2 raw11323step2Labels := by
      have ha : raw11323step2 = -raw11323step1 := by apply Matrix.ext; change ∀ i j, raw11323step2 i j = -(raw11323step1 i j); unfold raw11323step2 raw11323step1; decide +kernel
      have hl : raw11323step2Labels = raw11323step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11323step2 raw11323step2Labels = mixedMoment B raw11323step3 raw11323step3Labels := by
      have ha : raw11323step3 = raw11323step2 := by apply Matrix.ext; unfold raw11323step3 raw11323step2; decide +kernel
      have hl : raw11323step2Labels = labelEmbedding8 ∘ raw11323step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11323step2 raw11323step2Labels raw11323step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw11324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11324step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11324step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11324step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11324step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11324 raw11324Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11324 raw11324Labels = mixedMoment B raw11324step0 raw11324step0Labels := by
      have hz : ∀ j, raw11324 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11324step0 = (fun i j => raw11324 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11324step0 raw11324; decide +kernel
      have hl : raw11324step0Labels = raw11324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11324 raw11324Labels permutation434 hz
    mixedMoment B raw11324step0 raw11324step0Labels = mixedMoment B raw11324step1 raw11324step1Labels := by
      have ha : raw11324step1 = (fun i j => raw11324step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11324step1 raw11324step0; decide +kernel
      have hl : raw11324step1Labels = raw11324step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11324step0 raw11324step0Labels permutation49 permutation5
    mixedMoment B raw11324step1 raw11324step1Labels = mixedMoment B raw11324step2 raw11324step2Labels := by
      have ha : raw11324step2 = -raw11324step1 := by apply Matrix.ext; change ∀ i j, raw11324step2 i j = -(raw11324step1 i j); unfold raw11324step2 raw11324step1; decide +kernel
      have hl : raw11324step2Labels = raw11324step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11324step2 raw11324step2Labels = mixedMoment B raw11324step3 raw11324step3Labels := by
      have ha : raw11324step3 = raw11324step2 := by apply Matrix.ext; unfold raw11324step3 raw11324step2; decide +kernel
      have hl : raw11324step2Labels = labelEmbedding8 ∘ raw11324step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11324step2 raw11324step2Labels raw11324step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw11325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11325step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11325step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11325 raw11325Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw11325 raw11325Labels = mixedMoment B raw11325step0 raw11325step0Labels := by
      have hz : ∀ j, raw11325 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11325step0 = (fun i j => raw11325 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11325step0 raw11325; decide +kernel
      have hl : raw11325step0Labels = raw11325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11325 raw11325Labels permutation434 hz
    mixedMoment B raw11325step0 raw11325step0Labels = mixedMoment B raw11325step1 raw11325step1Labels := by
      have ha : raw11325step1 = (fun i j => raw11325step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11325step1 raw11325step0; decide +kernel
      have hl : raw11325step1Labels = raw11325step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11325step0 raw11325step0Labels permutation34 permutation3
    mixedMoment B raw11325step1 raw11325step1Labels = mixedMoment B raw11325step2 raw11325step2Labels := by
      have ha : raw11325step2 = raw11325step1 := by apply Matrix.ext; unfold raw11325step2 raw11325step1; decide +kernel
      have hl : raw11325step1Labels = labelEmbedding6 ∘ raw11325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11325step1 raw11325step1Labels raw11325step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

def raw11326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11326step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11326step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11326 raw11326Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11326 raw11326Labels = mixedMoment B raw11326step0 raw11326step0Labels := by
      have hz : ∀ j, raw11326 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11326step0 = (fun i j => raw11326 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11326step0 raw11326; decide +kernel
      have hl : raw11326step0Labels = raw11326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11326 raw11326Labels permutation434 hz
    mixedMoment B raw11326step0 raw11326step0Labels = mixedMoment B raw11326step1 raw11326step1Labels := by
      have ha : raw11326step1 = (fun i j => raw11326step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11326step1 raw11326step0; decide +kernel
      have hl : raw11326step1Labels = raw11326step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11326step0 raw11326step0Labels permutation34 permutation3
    mixedMoment B raw11326step1 raw11326step1Labels = mixedMoment B raw11326step2 raw11326step2Labels := by
      have ha : raw11326step2 = raw11326step1 := by apply Matrix.ext; unfold raw11326step2 raw11326step1; decide +kernel
      have hl : raw11326step1Labels = labelEmbedding6 ∘ raw11326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11326step1 raw11326step1Labels raw11326step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw11327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11327step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11327 raw11327Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw11327 raw11327Labels = mixedMoment B raw11327step0 raw11327step0Labels := by
      have ha : raw11327step0 = (fun i j => raw11327 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11327step0 raw11327; decide +kernel
      have hl : raw11327step0Labels = raw11327Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11327 raw11327Labels permutation202 permutation3
    mixedMoment B raw11327step0 raw11327step0Labels = mixedMoment B raw11327step1 raw11327step1Labels := by
      have ha : raw11327step1 = raw11327step0 := by apply Matrix.ext; unfold raw11327step1 raw11327step0; decide +kernel
      have hl : raw11327step0Labels = labelEmbedding6 ∘ raw11327step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11327step0 raw11327step0Labels raw11327step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

def raw11328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw11328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw11328step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11328step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11328step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11328step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11328 raw11328Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11328 raw11328Labels = mixedMoment B raw11328step0 raw11328step0Labels := by
      have hz : ∀ j, raw11328 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11328step0 = (fun i j => raw11328 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11328step0 raw11328; decide +kernel
      have hl : raw11328step0Labels = raw11328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11328 raw11328Labels permutation434 hz
    mixedMoment B raw11328step0 raw11328step0Labels = mixedMoment B raw11328step1 raw11328step1Labels := by
      have ha : raw11328step1 = (fun i j => raw11328step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11328step1 raw11328step0; decide +kernel
      have hl : raw11328step1Labels = raw11328step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11328step0 raw11328step0Labels permutation45 permutation5
    mixedMoment B raw11328step1 raw11328step1Labels = mixedMoment B raw11328step2 raw11328step2Labels := by
      have ha : raw11328step2 = -raw11328step1 := by apply Matrix.ext; change ∀ i j, raw11328step2 i j = -(raw11328step1 i j); unfold raw11328step2 raw11328step1; decide +kernel
      have hl : raw11328step2Labels = raw11328step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11328step2 raw11328step2Labels = mixedMoment B raw11328step3 raw11328step3Labels := by
      have ha : raw11328step3 = raw11328step2 := by apply Matrix.ext; unfold raw11328step3 raw11328step2; decide +kernel
      have hl : raw11328step2Labels = labelEmbedding8 ∘ raw11328step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11328step2 raw11328step2Labels raw11328step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw11329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11329step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11329step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11329step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11329step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11329 raw11329Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11329 raw11329Labels = mixedMoment B raw11329step0 raw11329step0Labels := by
      have hz : ∀ j, raw11329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11329step0 = (fun i j => raw11329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11329step0 raw11329; decide +kernel
      have hl : raw11329step0Labels = raw11329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11329 raw11329Labels permutation434 hz
    mixedMoment B raw11329step0 raw11329step0Labels = mixedMoment B raw11329step1 raw11329step1Labels := by
      have ha : raw11329step1 = (fun i j => raw11329step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11329step1 raw11329step0; decide +kernel
      have hl : raw11329step1Labels = raw11329step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11329step0 raw11329step0Labels permutation48 permutation5
    mixedMoment B raw11329step1 raw11329step1Labels = mixedMoment B raw11329step2 raw11329step2Labels := by
      have ha : raw11329step2 = -raw11329step1 := by apply Matrix.ext; change ∀ i j, raw11329step2 i j = -(raw11329step1 i j); unfold raw11329step2 raw11329step1; decide +kernel
      have hl : raw11329step2Labels = raw11329step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11329step2 raw11329step2Labels = mixedMoment B raw11329step3 raw11329step3Labels := by
      have ha : raw11329step3 = raw11329step2 := by apply Matrix.ext; unfold raw11329step3 raw11329step2; decide +kernel
      have hl : raw11329step2Labels = labelEmbedding8 ∘ raw11329step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11329step2 raw11329step2Labels raw11329step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw11330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11330step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11330 raw11330Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw11330 raw11330Labels = mixedMoment B raw11330step0 raw11330step0Labels := by
      have ha : raw11330step0 = (fun i j => raw11330 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11330step0 raw11330; decide +kernel
      have hl : raw11330step0Labels = raw11330Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11330 raw11330Labels permutation154 permutation3
    mixedMoment B raw11330step0 raw11330step0Labels = mixedMoment B raw11330step1 raw11330step1Labels := by
      have ha : raw11330step1 = raw11330step0 := by apply Matrix.ext; unfold raw11330step1 raw11330step0; decide +kernel
      have hl : raw11330step0Labels = labelEmbedding6 ∘ raw11330step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11330step0 raw11330step0Labels raw11330step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw11331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11331step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11331 raw11331Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11331 raw11331Labels = mixedMoment B raw11331step0 raw11331step0Labels := by
      have ha : raw11331step0 = (fun i j => raw11331 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11331step0 raw11331; decide +kernel
      have hl : raw11331step0Labels = raw11331Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11331 raw11331Labels permutation154 permutation3
    mixedMoment B raw11331step0 raw11331step0Labels = mixedMoment B raw11331step1 raw11331step1Labels := by
      have ha : raw11331step1 = raw11331step0 := by apply Matrix.ext; unfold raw11331step1 raw11331step0; decide +kernel
      have hl : raw11331step0Labels = labelEmbedding6 ∘ raw11331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11331step0 raw11331step0Labels raw11331step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw11332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11332step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11332 raw11332Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11332 raw11332Labels = mixedMoment B raw11332step0 raw11332step0Labels := by
      have ha : raw11332step0 = (fun i j => raw11332 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11332step0 raw11332; decide +kernel
      have hl : raw11332step0Labels = raw11332Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11332 raw11332Labels permutation178 permutation3
    mixedMoment B raw11332step0 raw11332step0Labels = mixedMoment B raw11332step1 raw11332step1Labels := by
      have ha : raw11332step1 = raw11332step0 := by apply Matrix.ext; unfold raw11332step1 raw11332step0; decide +kernel
      have hl : raw11332step0Labels = labelEmbedding6 ∘ raw11332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11332step0 raw11332step0Labels raw11332step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw11333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11333step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11333step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11333step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11333step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11333 raw11333Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw11333 raw11333Labels = mixedMoment B raw11333step0 raw11333step0Labels := by
      have ha : raw11333step0 = (fun i j => raw11333 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11333step0 raw11333; decide +kernel
      have hl : raw11333step0Labels = raw11333Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11333 raw11333Labels permutation224 permutation5
    mixedMoment B raw11333step0 raw11333step0Labels = mixedMoment B raw11333step1 raw11333step1Labels := by
      have ha : raw11333step1 = -raw11333step0 := by apply Matrix.ext; change ∀ i j, raw11333step1 i j = -(raw11333step0 i j); unfold raw11333step1 raw11333step0; decide +kernel
      have hl : raw11333step1Labels = raw11333step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11333step1 raw11333step1Labels = mixedMoment B raw11333step2 raw11333step2Labels := by
      have ha : raw11333step2 = raw11333step1 := by apply Matrix.ext; unfold raw11333step2 raw11333step1; decide +kernel
      have hl : raw11333step1Labels = labelEmbedding8 ∘ raw11333step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11333step1 raw11333step1Labels raw11333step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw11334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11334step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11334 raw11334Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw11334 raw11334Labels = mixedMoment B raw11334step0 raw11334step0Labels := by
      have ha : raw11334step0 = (fun i j => raw11334 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11334step0 raw11334; decide +kernel
      have hl : raw11334step0Labels = raw11334Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11334 raw11334Labels permutation155 permutation3
    mixedMoment B raw11334step0 raw11334step0Labels = mixedMoment B raw11334step1 raw11334step1Labels := by
      have ha : raw11334step1 = raw11334step0 := by apply Matrix.ext; unfold raw11334step1 raw11334step0; decide +kernel
      have hl : raw11334step0Labels = labelEmbedding6 ∘ raw11334step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11334step0 raw11334step0Labels raw11334step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw11335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw11335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11335step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11335step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11335 raw11335Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw11335 raw11335Labels = mixedMoment B raw11335step0 raw11335step0Labels := by
      have hz : ∀ j, raw11335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11335step0 = (fun i j => raw11335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11335step0 raw11335; decide +kernel
      have hl : raw11335step0Labels = raw11335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11335 raw11335Labels permutation434 hz
    mixedMoment B raw11335step0 raw11335step0Labels = mixedMoment B raw11335step1 raw11335step1Labels := by
      have ha : raw11335step1 = (fun i j => raw11335step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11335step1 raw11335step0; decide +kernel
      have hl : raw11335step1Labels = raw11335step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11335step0 raw11335step0Labels permutation32 permutation3
    mixedMoment B raw11335step1 raw11335step1Labels = mixedMoment B raw11335step2 raw11335step2Labels := by
      have ha : raw11335step2 = raw11335step1 := by apply Matrix.ext; unfold raw11335step2 raw11335step1; decide +kernel
      have hl : raw11335step1Labels = labelEmbedding6 ∘ raw11335step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11335step1 raw11335step1Labels raw11335step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

def raw11336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw11336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11336step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11336step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11336 raw11336Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw11336 raw11336Labels = mixedMoment B raw11336step0 raw11336step0Labels := by
      have hz : ∀ j, raw11336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11336step0 = (fun i j => raw11336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11336step0 raw11336; decide +kernel
      have hl : raw11336step0Labels = raw11336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11336 raw11336Labels permutation434 hz
    mixedMoment B raw11336step0 raw11336step0Labels = mixedMoment B raw11336step1 raw11336step1Labels := by
      have ha : raw11336step1 = (fun i j => raw11336step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11336step1 raw11336step0; decide +kernel
      have hl : raw11336step1Labels = raw11336step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11336step0 raw11336step0Labels permutation32 permutation3
    mixedMoment B raw11336step1 raw11336step1Labels = mixedMoment B raw11336step2 raw11336step2Labels := by
      have ha : raw11336step2 = raw11336step1 := by apply Matrix.ext; unfold raw11336step2 raw11336step1; decide +kernel
      have hl : raw11336step1Labels = labelEmbedding6 ∘ raw11336step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11336step1 raw11336step1Labels raw11336step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw11337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw11337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11337step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11337step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11337step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11337 raw11337Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw11337 raw11337Labels = mixedMoment B raw11337step0 raw11337step0Labels := by
      have hz : ∀ j, raw11337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11337step0 = (fun i j => raw11337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11337step0 raw11337; decide +kernel
      have hl : raw11337step0Labels = raw11337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11337 raw11337Labels permutation434 hz
    mixedMoment B raw11337step0 raw11337step0Labels = mixedMoment B raw11337step1 raw11337step1Labels := by
      have ha : raw11337step1 = (fun i j => raw11337step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11337step1 raw11337step0; decide +kernel
      have hl : raw11337step1Labels = raw11337step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11337step0 raw11337step0Labels permutation38 permutation3
    mixedMoment B raw11337step1 raw11337step1Labels = mixedMoment B raw11337step2 raw11337step2Labels := by
      have ha : raw11337step2 = raw11337step1 := by apply Matrix.ext; unfold raw11337step2 raw11337step1; decide +kernel
      have hl : raw11337step1Labels = labelEmbedding6 ∘ raw11337step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11337step1 raw11337step1Labels raw11337step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw11338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11338step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11338 raw11338Labels = mixedMoment B node4732 node4732Labels := by
  calc
    mixedMoment B raw11338 raw11338Labels = mixedMoment B raw11338step0 raw11338step0Labels := by
      have ha : raw11338step0 = (fun i j => raw11338 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11338step0 raw11338; decide +kernel
      have hl : raw11338step0Labels = raw11338Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11338 raw11338Labels permutation200 permutation3
    mixedMoment B raw11338step0 raw11338step0Labels = mixedMoment B raw11338step1 raw11338step1Labels := by
      have ha : raw11338step1 = raw11338step0 := by apply Matrix.ext; unfold raw11338step1 raw11338step0; decide +kernel
      have hl : raw11338step0Labels = labelEmbedding6 ∘ raw11338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11338step0 raw11338step0Labels raw11338step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4732 node4732Labels := by rfl

def raw11339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw11339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw11339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11339step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11339step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11339 raw11339Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11339 raw11339Labels = mixedMoment B raw11339step0 raw11339step0Labels := by
      have hz : ∀ j, raw11339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11339step0 = (fun i j => raw11339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11339step0 raw11339; decide +kernel
      have hl : raw11339step0Labels = raw11339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11339 raw11339Labels permutation434 hz
    mixedMoment B raw11339step0 raw11339step0Labels = mixedMoment B raw11339step1 raw11339step1Labels := by
      have ha : raw11339step1 = (fun i j => raw11339step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11339step1 raw11339step0; decide +kernel
      have hl : raw11339step1Labels = raw11339step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11339step0 raw11339step0Labels permutation33 permutation3
    mixedMoment B raw11339step1 raw11339step1Labels = mixedMoment B raw11339step2 raw11339step2Labels := by
      have ha : raw11339step2 = raw11339step1 := by apply Matrix.ext; unfold raw11339step2 raw11339step1; decide +kernel
      have hl : raw11339step1Labels = labelEmbedding6 ∘ raw11339step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11339step1 raw11339step1Labels raw11339step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw11340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw11340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11340step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11340step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11340 raw11340Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw11340 raw11340Labels = mixedMoment B raw11340step0 raw11340step0Labels := by
      have hz : ∀ j, raw11340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11340step0 = (fun i j => raw11340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11340step0 raw11340; decide +kernel
      have hl : raw11340step0Labels = raw11340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11340 raw11340Labels permutation434 hz
    mixedMoment B raw11340step0 raw11340step0Labels = mixedMoment B raw11340step1 raw11340step1Labels := by
      have ha : raw11340step1 = (fun i j => raw11340step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11340step1 raw11340step0; decide +kernel
      have hl : raw11340step1Labels = raw11340step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11340step0 raw11340step0Labels permutation32 permutation3
    mixedMoment B raw11340step1 raw11340step1Labels = mixedMoment B raw11340step2 raw11340step2Labels := by
      have ha : raw11340step2 = raw11340step1 := by apply Matrix.ext; unfold raw11340step2 raw11340step1; decide +kernel
      have hl : raw11340step1Labels = labelEmbedding6 ∘ raw11340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11340step1 raw11340step1Labels raw11340step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

def raw11341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw11341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11341step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11341 raw11341Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw11341 raw11341Labels = mixedMoment B raw11341step0 raw11341step0Labels := by
      have hz : ∀ j, raw11341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11341step0 = (fun i j => raw11341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11341step0 raw11341; decide +kernel
      have hl : raw11341step0Labels = raw11341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11341 raw11341Labels permutation434 hz
    mixedMoment B raw11341step0 raw11341step0Labels = mixedMoment B raw11341step1 raw11341step1Labels := by
      have ha : raw11341step1 = (fun i j => raw11341step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11341step1 raw11341step0; decide +kernel
      have hl : raw11341step1Labels = raw11341step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11341step0 raw11341step0Labels permutation32 permutation3
    mixedMoment B raw11341step1 raw11341step1Labels = mixedMoment B raw11341step2 raw11341step2Labels := by
      have ha : raw11341step2 = raw11341step1 := by apply Matrix.ext; unfold raw11341step2 raw11341step1; decide +kernel
      have hl : raw11341step1Labels = labelEmbedding6 ∘ raw11341step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11341step1 raw11341step1Labels raw11341step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw11342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw11342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11342step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11342step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11342 raw11342Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw11342 raw11342Labels = mixedMoment B raw11342step0 raw11342step0Labels := by
      have hz : ∀ j, raw11342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11342step0 = (fun i j => raw11342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11342step0 raw11342; decide +kernel
      have hl : raw11342step0Labels = raw11342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11342 raw11342Labels permutation434 hz
    mixedMoment B raw11342step0 raw11342step0Labels = mixedMoment B raw11342step1 raw11342step1Labels := by
      have ha : raw11342step1 = (fun i j => raw11342step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11342step1 raw11342step0; decide +kernel
      have hl : raw11342step1Labels = raw11342step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11342step0 raw11342step0Labels permutation38 permutation3
    mixedMoment B raw11342step1 raw11342step1Labels = mixedMoment B raw11342step2 raw11342step2Labels := by
      have ha : raw11342step2 = raw11342step1 := by apply Matrix.ext; unfold raw11342step2 raw11342step1; decide +kernel
      have hl : raw11342step1Labels = labelEmbedding6 ∘ raw11342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11342step1 raw11342step1Labels raw11342step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw11343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11343step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11343step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11343 raw11343Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw11343 raw11343Labels = mixedMoment B raw11343step0 raw11343step0Labels := by
      have ha : raw11343step0 = (fun i j => raw11343 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11343step0 raw11343; decide +kernel
      have hl : raw11343step0Labels = raw11343Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11343 raw11343Labels permutation200 permutation3
    mixedMoment B raw11343step0 raw11343step0Labels = mixedMoment B raw11343step1 raw11343step1Labels := by
      have ha : raw11343step1 = raw11343step0 := by apply Matrix.ext; unfold raw11343step1 raw11343step0; decide +kernel
      have hl : raw11343step0Labels = labelEmbedding6 ∘ raw11343step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11343step0 raw11343step0Labels raw11343step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

def raw11344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw11344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw11344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw11344step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11344step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw11344step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11344step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw11344step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11344 raw11344Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw11344 raw11344Labels = mixedMoment B raw11344step0 raw11344step0Labels := by
      have hz : ∀ j, raw11344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11344step0 = (fun i j => raw11344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11344step0 raw11344; decide +kernel
      have hl : raw11344step0Labels = raw11344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11344 raw11344Labels permutation434 hz
    mixedMoment B raw11344step0 raw11344step0Labels = mixedMoment B raw11344step1 raw11344step1Labels := by
      have ha : raw11344step1 = (fun i j => raw11344step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11344step1 raw11344step0; decide +kernel
      have hl : raw11344step1Labels = raw11344step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11344step0 raw11344step0Labels permutation44 permutation5
    mixedMoment B raw11344step1 raw11344step1Labels = mixedMoment B raw11344step2 raw11344step2Labels := by
      have ha : raw11344step2 = -raw11344step1 := by apply Matrix.ext; change ∀ i j, raw11344step2 i j = -(raw11344step1 i j); unfold raw11344step2 raw11344step1; decide +kernel
      have hl : raw11344step2Labels = raw11344step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11344step2 raw11344step2Labels = mixedMoment B raw11344step3 raw11344step3Labels := by
      have ha : raw11344step3 = raw11344step2 := by apply Matrix.ext; unfold raw11344step3 raw11344step2; decide +kernel
      have hl : raw11344step2Labels = labelEmbedding8 ∘ raw11344step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11344step2 raw11344step2Labels raw11344step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw11345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11345step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11345 raw11345Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw11345 raw11345Labels = mixedMoment B raw11345step0 raw11345step0Labels := by
      have hz : ∀ j, raw11345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11345step0 = (fun i j => raw11345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11345step0 raw11345; decide +kernel
      have hl : raw11345step0Labels = raw11345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11345 raw11345Labels permutation434 hz
    mixedMoment B raw11345step0 raw11345step0Labels = mixedMoment B raw11345step1 raw11345step1Labels := by
      have ha : raw11345step1 = (fun i j => raw11345step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11345step1 raw11345step0; decide +kernel
      have hl : raw11345step1Labels = raw11345step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11345step0 raw11345step0Labels permutation32 permutation3
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw11346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11346step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11346 raw11346Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw11346 raw11346Labels = mixedMoment B raw11346step0 raw11346step0Labels := by
      have hz : ∀ j, raw11346 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11346step0 = (fun i j => raw11346 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11346step0 raw11346; decide +kernel
      have hl : raw11346step0Labels = raw11346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11346 raw11346Labels permutation434 hz
    mixedMoment B raw11346step0 raw11346step0Labels = mixedMoment B raw11346step1 raw11346step1Labels := by
      have ha : raw11346step1 = (fun i j => raw11346step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11346step1 raw11346step0; decide +kernel
      have hl : raw11346step1Labels = raw11346step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11346step0 raw11346step0Labels permutation38 permutation3
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw11347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11347 raw11347Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw11347 raw11347Labels = mixedMoment B raw11347step0 raw11347step0Labels := by
      have ha : raw11347step0 = (fun i j => raw11347 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11347step0 raw11347; decide +kernel
      have hl : raw11347step0Labels = raw11347Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11347 raw11347Labels permutation200 permutation3
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw11348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw11348step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11348 raw11348Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw11348 raw11348Labels = mixedMoment B raw11348step0 raw11348step0Labels := by
      have hz : ∀ j, raw11348 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11348step0 = (fun i j => raw11348 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11348step0 raw11348; decide +kernel
      have hl : raw11348step0Labels = raw11348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11348 raw11348Labels permutation434 hz
    mixedMoment B raw11348step0 raw11348step0Labels = mixedMoment B raw11348step1 raw11348step1Labels := by
      have ha : raw11348step1 = (fun i j => raw11348step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11348step1 raw11348step0; decide +kernel
      have hl : raw11348step1Labels = raw11348step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11348step0 raw11348step0Labels permutation44 permutation3
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw11349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11349step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw11349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11349 raw11349Labels = mixedMoment B node3911 node3911Labels := by
  calc
    mixedMoment B raw11349 raw11349Labels = mixedMoment B raw11349step0 raw11349step0Labels := by
      have hz : ∀ j, raw11349 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11349step0 = (fun i j => raw11349 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11349step0 raw11349; decide +kernel
      have hl : raw11349step0Labels = raw11349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11349 raw11349Labels permutation434 hz
    mixedMoment B raw11349step0 raw11349step0Labels = mixedMoment B raw11349step1 raw11349step1Labels := by
      have ha : raw11349step1 = (fun i j => raw11349step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11349step1 raw11349step0; decide +kernel
      have hl : raw11349step1Labels = raw11349step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11349step0 raw11349step0Labels permutation32 permutation3
    _ = mixedMoment B node3911 node3911Labels := by rfl

def raw11350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11350step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11350 raw11350Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw11350 raw11350Labels = mixedMoment B raw11350step0 raw11350step0Labels := by
      have hz : ∀ j, raw11350 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11350step0 = (fun i j => raw11350 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11350step0 raw11350; decide +kernel
      have hl : raw11350step0Labels = raw11350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11350 raw11350Labels permutation434 hz
    mixedMoment B raw11350step0 raw11350step0Labels = mixedMoment B raw11350step1 raw11350step1Labels := by
      have ha : raw11350step1 = (fun i j => raw11350step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11350step1 raw11350step0; decide +kernel
      have hl : raw11350step1Labels = raw11350step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11350step0 raw11350step0Labels permutation40 permutation3
    _ = mixedMoment B node807 node807Labels := by rfl

def raw11351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11351Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11351step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11351 raw11351Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw11351 raw11351Labels = mixedMoment B raw11351step0 raw11351step0Labels := by
      have hz : ∀ j, raw11351 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11351step0 = (fun i j => raw11351 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11351step0 raw11351; decide +kernel
      have hl : raw11351step0Labels = raw11351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11351 raw11351Labels permutation434 hz
    mixedMoment B raw11351step0 raw11351step0Labels = mixedMoment B raw11351step1 raw11351step1Labels := by
      have ha : raw11351step1 = (fun i j => raw11351step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11351step1 raw11351step0; decide +kernel
      have hl : raw11351step1Labels = raw11351step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11351step0 raw11351step0Labels permutation40 permutation3
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw11352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11352Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11352 raw11352Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw11352 raw11352Labels = mixedMoment B raw11352step0 raw11352step0Labels := by
      have ha : raw11352step0 = (fun i j => raw11352 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11352step0 raw11352; decide +kernel
      have hl : raw11352step0Labels = raw11352Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11352 raw11352Labels permutation208 permutation3
    _ = mixedMoment B node1909 node1909Labels := by rfl

def raw11353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11353Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw11353step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw11353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11353 raw11353Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw11353 raw11353Labels = mixedMoment B raw11353step0 raw11353step0Labels := by
      have hz : ∀ j, raw11353 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11353step0 = (fun i j => raw11353 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11353step0 raw11353; decide +kernel
      have hl : raw11353step0Labels = raw11353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11353 raw11353Labels permutation434 hz
    mixedMoment B raw11353step0 raw11353step0Labels = mixedMoment B raw11353step1 raw11353step1Labels := by
      have ha : raw11353step1 = (fun i j => raw11353step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11353step1 raw11353step0; decide +kernel
      have hl : raw11353step1Labels = raw11353step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11353step0 raw11353step0Labels permutation46 permutation3
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw11354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11354step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11354 raw11354Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw11354 raw11354Labels = mixedMoment B raw11354step0 raw11354step0Labels := by
      have hz : ∀ j, raw11354 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11354step0 = (fun i j => raw11354 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11354step0 raw11354; decide +kernel
      have hl : raw11354step0Labels = raw11354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11354 raw11354Labels permutation434 hz
    mixedMoment B raw11354step0 raw11354step0Labels = mixedMoment B raw11354step1 raw11354step1Labels := by
      have ha : raw11354step1 = (fun i j => raw11354step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11354step1 raw11354step0; decide +kernel
      have hl : raw11354step1Labels = raw11354step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11354step0 raw11354step0Labels permutation41 permutation3
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw11355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11355step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11355 raw11355Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw11355 raw11355Labels = mixedMoment B raw11355step0 raw11355step0Labels := by
      have hz : ∀ j, raw11355 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11355step0 = (fun i j => raw11355 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11355step0 raw11355; decide +kernel
      have hl : raw11355step0Labels = raw11355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11355 raw11355Labels permutation434 hz
    mixedMoment B raw11355step0 raw11355step0Labels = mixedMoment B raw11355step1 raw11355step1Labels := by
      have ha : raw11355step1 = (fun i j => raw11355step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11355step1 raw11355step0; decide +kernel
      have hl : raw11355step1Labels = raw11355step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11355step0 raw11355step0Labels permutation34 permutation3
    _ = mixedMoment B node807 node807Labels := by rfl

def raw11356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11356 raw11356Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw11356 raw11356Labels = mixedMoment B raw11356step0 raw11356step0Labels := by
      have hz : ∀ j, raw11356 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11356step0 = (fun i j => raw11356 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11356step0 raw11356; decide +kernel
      have hl : raw11356step0Labels = raw11356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11356 raw11356Labels permutation434 hz
    mixedMoment B raw11356step0 raw11356step0Labels = mixedMoment B raw11356step1 raw11356step1Labels := by
      have ha : raw11356step1 = (fun i j => raw11356step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11356step1 raw11356step0; decide +kernel
      have hl : raw11356step1Labels = raw11356step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11356step0 raw11356step0Labels permutation34 permutation3
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw11357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11357 raw11357Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw11357 raw11357Labels = mixedMoment B raw11357step0 raw11357step0Labels := by
      have ha : raw11357step0 = (fun i j => raw11357 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11357step0 raw11357; decide +kernel
      have hl : raw11357step0Labels = raw11357Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11357 raw11357Labels permutation202 permutation3
    _ = mixedMoment B node1909 node1909Labels := by rfl

def raw11358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw11358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw11358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11358 raw11358Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw11358 raw11358Labels = mixedMoment B raw11358step0 raw11358step0Labels := by
      have hz : ∀ j, raw11358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11358step0 = (fun i j => raw11358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11358step0 raw11358; decide +kernel
      have hl : raw11358step0Labels = raw11358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11358 raw11358Labels permutation434 hz
    mixedMoment B raw11358step0 raw11358step0Labels = mixedMoment B raw11358step1 raw11358step1Labels := by
      have ha : raw11358step1 = (fun i j => raw11358step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11358step1 raw11358step0; decide +kernel
      have hl : raw11358step1Labels = raw11358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11358step0 raw11358step0Labels permutation44 permutation3
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw11359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11359step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11359 raw11359Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw11359 raw11359Labels = mixedMoment B raw11359step0 raw11359step0Labels := by
      have hz : ∀ j, raw11359 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11359step0 = (fun i j => raw11359 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11359step0 raw11359; decide +kernel
      have hl : raw11359step0Labels = raw11359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11359 raw11359Labels permutation434 hz
    mixedMoment B raw11359step0 raw11359step0Labels = mixedMoment B raw11359step1 raw11359step1Labels := by
      have ha : raw11359step1 = (fun i j => raw11359step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11359step1 raw11359step0; decide +kernel
      have hl : raw11359step1Labels = raw11359step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11359step0 raw11359step0Labels permutation35 permutation3
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw11360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11360 raw11360Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw11360 raw11360Labels = mixedMoment B raw11360step0 raw11360step0Labels := by
      have ha : raw11360step0 = (fun i j => raw11360 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11360step0 raw11360; decide +kernel
      have hl : raw11360step0Labels = raw11360Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11360 raw11360Labels permutation154 permutation3
    _ = mixedMoment B node783 node783Labels := by rfl

def raw11361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11361 raw11361Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw11361 raw11361Labels = mixedMoment B raw11361step0 raw11361step0Labels := by
      have ha : raw11361step0 = (fun i j => raw11361 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11361step0 raw11361; decide +kernel
      have hl : raw11361step0Labels = raw11361Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11361 raw11361Labels permutation154 permutation3
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw11362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11362 raw11362Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw11362 raw11362Labels = mixedMoment B raw11362step0 raw11362step0Labels := by
      have ha : raw11362step0 = (fun i j => raw11362 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11362step0 raw11362; decide +kernel
      have hl : raw11362step0Labels = raw11362Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11362 raw11362Labels permutation178 permutation3
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw11363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11363 raw11363Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw11363 raw11363Labels = mixedMoment B raw11363step0 raw11363step0Labels := by
      have ha : raw11363step0 = (fun i j => raw11363 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11363step0 raw11363; decide +kernel
      have hl : raw11363step0Labels = raw11363Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11363 raw11363Labels permutation224 permutation3
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw11364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11364 raw11364Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw11364 raw11364Labels = mixedMoment B raw11364step0 raw11364step0Labels := by
      have ha : raw11364step0 = (fun i j => raw11364 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11364step0 raw11364; decide +kernel
      have hl : raw11364step0Labels = raw11364Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11364 raw11364Labels permutation155 permutation3
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw11365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw11365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11365 raw11365Labels = mixedMoment B node790 node790Labels := by
  calc
    mixedMoment B raw11365 raw11365Labels = mixedMoment B raw11365step0 raw11365step0Labels := by
      have hz : ∀ j, raw11365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11365step0 = (fun i j => raw11365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11365step0 raw11365; decide +kernel
      have hl : raw11365step0Labels = raw11365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11365 raw11365Labels permutation434 hz
    mixedMoment B raw11365step0 raw11365step0Labels = mixedMoment B raw11365step1 raw11365step1Labels := by
      have ha : raw11365step1 = (fun i j => raw11365step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11365step1 raw11365step0; decide +kernel
      have hl : raw11365step1Labels = raw11365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11365step0 raw11365step0Labels permutation32 permutation3
    _ = mixedMoment B node790 node790Labels := by rfl

def raw11366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw11366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11366 raw11366Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw11366 raw11366Labels = mixedMoment B raw11366step0 raw11366step0Labels := by
      have hz : ∀ j, raw11366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11366step0 = (fun i j => raw11366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11366step0 raw11366; decide +kernel
      have hl : raw11366step0Labels = raw11366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11366 raw11366Labels permutation434 hz
    mixedMoment B raw11366step0 raw11366step0Labels = mixedMoment B raw11366step1 raw11366step1Labels := by
      have ha : raw11366step1 = (fun i j => raw11366step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11366step1 raw11366step0; decide +kernel
      have hl : raw11366step1Labels = raw11366step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11366step0 raw11366step0Labels permutation32 permutation3
    _ = mixedMoment B node2029 node2029Labels := by rfl

def raw11367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw11367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11367 raw11367Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw11367 raw11367Labels = mixedMoment B raw11367step0 raw11367step0Labels := by
      have hz : ∀ j, raw11367 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11367step0 = (fun i j => raw11367 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11367step0 raw11367; decide +kernel
      have hl : raw11367step0Labels = raw11367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11367 raw11367Labels permutation434 hz
    mixedMoment B raw11367step0 raw11367step0Labels = mixedMoment B raw11367step1 raw11367step1Labels := by
      have ha : raw11367step1 = (fun i j => raw11367step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11367step1 raw11367step0; decide +kernel
      have hl : raw11367step1Labels = raw11367step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11367step0 raw11367step0Labels permutation38 permutation3
    _ = mixedMoment B node2029 node2029Labels := by rfl

def raw11368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11368 raw11368Labels = mixedMoment B node1901 node1901Labels := by
  calc
    mixedMoment B raw11368 raw11368Labels = mixedMoment B raw11368step0 raw11368step0Labels := by
      have ha : raw11368step0 = (fun i j => raw11368 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11368step0 raw11368; decide +kernel
      have hl : raw11368step0Labels = raw11368Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11368 raw11368Labels permutation200 permutation3
    _ = mixedMoment B node1901 node1901Labels := by rfl

def raw11369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw11369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw11369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11369 raw11369Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw11369 raw11369Labels = mixedMoment B raw11369step0 raw11369step0Labels := by
      have hz : ∀ j, raw11369 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11369step0 = (fun i j => raw11369 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11369step0 raw11369; decide +kernel
      have hl : raw11369step0Labels = raw11369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11369 raw11369Labels permutation434 hz
    mixedMoment B raw11369step0 raw11369step0Labels = mixedMoment B raw11369step1 raw11369step1Labels := by
      have ha : raw11369step1 = (fun i j => raw11369step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11369step1 raw11369step0; decide +kernel
      have hl : raw11369step1Labels = raw11369step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11369step0 raw11369step0Labels permutation33 permutation3
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw11370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw11370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11370 raw11370Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw11370 raw11370Labels = mixedMoment B raw11370step0 raw11370step0Labels := by
      have hz : ∀ j, raw11370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11370step0 = (fun i j => raw11370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11370step0 raw11370; decide +kernel
      have hl : raw11370step0Labels = raw11370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11370 raw11370Labels permutation434 hz
    mixedMoment B raw11370step0 raw11370step0Labels = mixedMoment B raw11370step1 raw11370step1Labels := by
      have ha : raw11370step1 = (fun i j => raw11370step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11370step1 raw11370step0; decide +kernel
      have hl : raw11370step1Labels = raw11370step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11370step0 raw11370step0Labels permutation32 permutation3
    _ = mixedMoment B node785 node785Labels := by rfl

def raw11371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw11371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11371 raw11371Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw11371 raw11371Labels = mixedMoment B raw11371step0 raw11371step0Labels := by
      have hz : ∀ j, raw11371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11371step0 = (fun i j => raw11371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11371step0 raw11371; decide +kernel
      have hl : raw11371step0Labels = raw11371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11371 raw11371Labels permutation434 hz
    mixedMoment B raw11371step0 raw11371step0Labels = mixedMoment B raw11371step1 raw11371step1Labels := by
      have ha : raw11371step1 = (fun i j => raw11371step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11371step1 raw11371step0; decide +kernel
      have hl : raw11371step1Labels = raw11371step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11371step0 raw11371step0Labels permutation32 permutation3
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw11372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw11372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11372 raw11372Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw11372 raw11372Labels = mixedMoment B raw11372step0 raw11372step0Labels := by
      have hz : ∀ j, raw11372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11372step0 = (fun i j => raw11372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11372step0 raw11372; decide +kernel
      have hl : raw11372step0Labels = raw11372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11372 raw11372Labels permutation434 hz
    mixedMoment B raw11372step0 raw11372step0Labels = mixedMoment B raw11372step1 raw11372step1Labels := by
      have ha : raw11372step1 = (fun i j => raw11372step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11372step1 raw11372step0; decide +kernel
      have hl : raw11372step1Labels = raw11372step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11372step0 raw11372step0Labels permutation38 permutation3
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw11373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11373 raw11373Labels = mixedMoment B node1897 node1897Labels := by
  calc
    mixedMoment B raw11373 raw11373Labels = mixedMoment B raw11373step0 raw11373step0Labels := by
      have ha : raw11373step0 = (fun i j => raw11373 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11373step0 raw11373; decide +kernel
      have hl : raw11373step0Labels = raw11373Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11373 raw11373Labels permutation200 permutation3
    _ = mixedMoment B node1897 node1897Labels := by rfl

def raw11374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw11374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw11374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw11374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11374 raw11374Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw11374 raw11374Labels = mixedMoment B raw11374step0 raw11374step0Labels := by
      have hz : ∀ j, raw11374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11374step0 = (fun i j => raw11374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11374step0 raw11374; decide +kernel
      have hl : raw11374step0Labels = raw11374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11374 raw11374Labels permutation434 hz
    mixedMoment B raw11374step0 raw11374step0Labels = mixedMoment B raw11374step1 raw11374step1Labels := by
      have ha : raw11374step1 = (fun i j => raw11374step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11374step1 raw11374step0; decide +kernel
      have hl : raw11374step1Labels = raw11374step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11374step0 raw11374step0Labels permutation44 permutation3
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw11375 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11375step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11375step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11375step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11375step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11375step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11375 raw11375Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw11375 raw11375Labels = mixedMoment B raw11375step0 raw11375step0Labels := by
      have hz : ∀ j, raw11375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11375step0 = (fun i j => raw11375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11375step0 raw11375; decide +kernel
      have hl : raw11375step0Labels = raw11375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11375 raw11375Labels permutation434 hz
    mixedMoment B raw11375step0 raw11375step0Labels = mixedMoment B raw11375step1 raw11375step1Labels := by
      have hz : ∀ j, raw11375step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11375step1 = (fun i j => raw11375step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11375step1 raw11375step0; decide +kernel
      have hl : raw11375step1Labels = raw11375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11375step0 raw11375step0Labels permutation80 hz
    mixedMoment B raw11375step1 raw11375step1Labels = mixedMoment B raw11375step2 raw11375step2Labels := by
      have ha : raw11375step2 = (fun i j => raw11375step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11375step2 raw11375step1; decide +kernel
      have hl : raw11375step2Labels = raw11375step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11375step1 raw11375step1Labels permutation11 permutation4
    mixedMoment B raw11375step2 raw11375step2Labels = mixedMoment B raw11375step3 raw11375step3Labels := by
      have ha : raw11375step3 = -raw11375step2 := by apply Matrix.ext; change ∀ i j, raw11375step3 i j = -(raw11375step2 i j); unfold raw11375step3 raw11375step2; decide +kernel
      have hl : raw11375step3Labels = raw11375step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11375step3 raw11375step3Labels = mixedMoment B raw11375step4 raw11375step4Labels := by
      have ha : raw11375step4 = raw11375step3 := by apply Matrix.ext; unfold raw11375step4 raw11375step3; decide +kernel
      have hl : raw11375step3Labels = labelEmbedding7 ∘ raw11375step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11375step3 raw11375step3Labels raw11375step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw11376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw11376step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11376step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11376step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11376step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11376 raw11376Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw11376 raw11376Labels = mixedMoment B raw11376step0 raw11376step0Labels := by
      have hz : ∀ j, raw11376 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11376step0 = (fun i j => raw11376 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11376step0 raw11376; decide +kernel
      have hl : raw11376step0Labels = raw11376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11376 raw11376Labels permutation434 hz
    mixedMoment B raw11376step0 raw11376step0Labels = mixedMoment B raw11376step1 raw11376step1Labels := by
      have ha : raw11376step1 = (fun i j => raw11376step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11376step1 raw11376step0; decide +kernel
      have hl : raw11376step1Labels = raw11376step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11376step0 raw11376step0Labels permutation45 permutation4
    mixedMoment B raw11376step1 raw11376step1Labels = mixedMoment B raw11376step2 raw11376step2Labels := by
      have ha : raw11376step2 = -raw11376step1 := by apply Matrix.ext; change ∀ i j, raw11376step2 i j = -(raw11376step1 i j); unfold raw11376step2 raw11376step1; decide +kernel
      have hl : raw11376step2Labels = raw11376step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11376step2 raw11376step2Labels = mixedMoment B raw11376step3 raw11376step3Labels := by
      have ha : raw11376step3 = raw11376step2 := by apply Matrix.ext; unfold raw11376step3 raw11376step2; decide +kernel
      have hl : raw11376step2Labels = labelEmbedding7 ∘ raw11376step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11376step2 raw11376step2Labels raw11376step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw11377 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11377step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11377step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11377step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11377step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11377step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11377step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11377 raw11377Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw11377 raw11377Labels = mixedMoment B raw11377step0 raw11377step0Labels := by
      have hz : ∀ j, raw11377 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11377step0 = (fun i j => raw11377 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11377step0 raw11377; decide +kernel
      have hl : raw11377step0Labels = raw11377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11377 raw11377Labels permutation434 hz
    mixedMoment B raw11377step0 raw11377step0Labels = mixedMoment B raw11377step1 raw11377step1Labels := by
      have hz : ∀ j, raw11377step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11377step1 = (fun i j => raw11377step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11377step1 raw11377step0; decide +kernel
      have hl : raw11377step1Labels = raw11377step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11377step0 raw11377step0Labels permutation56 hz
    mixedMoment B raw11377step1 raw11377step1Labels = mixedMoment B raw11377step2 raw11377step2Labels := by
      have ha : raw11377step2 = (fun i j => raw11377step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11377step2 raw11377step1; decide +kernel
      have hl : raw11377step2Labels = raw11377step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11377step1 raw11377step1Labels permutation11 permutation4
    mixedMoment B raw11377step2 raw11377step2Labels = mixedMoment B raw11377step3 raw11377step3Labels := by
      have ha : raw11377step3 = -raw11377step2 := by apply Matrix.ext; change ∀ i j, raw11377step3 i j = -(raw11377step2 i j); unfold raw11377step3 raw11377step2; decide +kernel
      have hl : raw11377step3Labels = raw11377step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11377step3 raw11377step3Labels = mixedMoment B raw11377step4 raw11377step4Labels := by
      have ha : raw11377step4 = raw11377step3 := by apply Matrix.ext; unfold raw11377step4 raw11377step3; decide +kernel
      have hl : raw11377step3Labels = labelEmbedding7 ∘ raw11377step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11377step3 raw11377step3Labels raw11377step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw11378 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw11378step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11378step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11378step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11378step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11378 raw11378Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw11378 raw11378Labels = mixedMoment B raw11378step0 raw11378step0Labels := by
      have ha : raw11378step0 = (fun i j => raw11378 (permutation213 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11378step0 raw11378; decide +kernel
      have hl : raw11378step0Labels = raw11378Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11378 raw11378Labels permutation213 permutation4
    mixedMoment B raw11378step0 raw11378step0Labels = mixedMoment B raw11378step1 raw11378step1Labels := by
      have ha : raw11378step1 = -raw11378step0 := by apply Matrix.ext; change ∀ i j, raw11378step1 i j = -(raw11378step0 i j); unfold raw11378step1 raw11378step0; decide +kernel
      have hl : raw11378step1Labels = raw11378step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11378step1 raw11378step1Labels = mixedMoment B raw11378step2 raw11378step2Labels := by
      have ha : raw11378step2 = raw11378step1 := by apply Matrix.ext; unfold raw11378step2 raw11378step1; decide +kernel
      have hl : raw11378step1Labels = labelEmbedding7 ∘ raw11378step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11378step1 raw11378step1Labels raw11378step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw11379 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw11379step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11379step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11379step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11379step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11379step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11379 raw11379Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw11379 raw11379Labels = mixedMoment B raw11379step0 raw11379step0Labels := by
      have hz : ∀ j, raw11379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11379step0 = (fun i j => raw11379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11379step0 raw11379; decide +kernel
      have hl : raw11379step0Labels = raw11379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11379 raw11379Labels permutation434 hz
    mixedMoment B raw11379step0 raw11379step0Labels = mixedMoment B raw11379step1 raw11379step1Labels := by
      have ha : raw11379step1 = (fun i j => raw11379step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11379step1 raw11379step0; decide +kernel
      have hl : raw11379step1Labels = raw11379step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11379step0 raw11379step0Labels permutation45 permutation4
    mixedMoment B raw11379step1 raw11379step1Labels = mixedMoment B raw11379step2 raw11379step2Labels := by
      have ha : raw11379step2 = -raw11379step1 := by apply Matrix.ext; change ∀ i j, raw11379step2 i j = -(raw11379step1 i j); unfold raw11379step2 raw11379step1; decide +kernel
      have hl : raw11379step2Labels = raw11379step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11379step2 raw11379step2Labels = mixedMoment B raw11379step3 raw11379step3Labels := by
      have ha : raw11379step3 = raw11379step2 := by apply Matrix.ext; unfold raw11379step3 raw11379step2; decide +kernel
      have hl : raw11379step2Labels = labelEmbedding7 ∘ raw11379step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11379step2 raw11379step2Labels raw11379step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw11380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw11380step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11380step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11380step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11380step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11380 raw11380Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw11380 raw11380Labels = mixedMoment B raw11380step0 raw11380step0Labels := by
      have hz : ∀ j, raw11380 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11380step0 = (fun i j => raw11380 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11380step0 raw11380; decide +kernel
      have hl : raw11380step0Labels = raw11380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11380 raw11380Labels permutation434 hz
    mixedMoment B raw11380step0 raw11380step0Labels = mixedMoment B raw11380step1 raw11380step1Labels := by
      have ha : raw11380step1 = (fun i j => raw11380step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11380step1 raw11380step0; decide +kernel
      have hl : raw11380step1Labels = raw11380step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11380step0 raw11380step0Labels permutation44 permutation4
    mixedMoment B raw11380step1 raw11380step1Labels = mixedMoment B raw11380step2 raw11380step2Labels := by
      have ha : raw11380step2 = -raw11380step1 := by apply Matrix.ext; change ∀ i j, raw11380step2 i j = -(raw11380step1 i j); unfold raw11380step2 raw11380step1; decide +kernel
      have hl : raw11380step2Labels = raw11380step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11380step2 raw11380step2Labels = mixedMoment B raw11380step3 raw11380step3Labels := by
      have ha : raw11380step3 = raw11380step2 := by apply Matrix.ext; unfold raw11380step3 raw11380step2; decide +kernel
      have hl : raw11380step2Labels = labelEmbedding7 ∘ raw11380step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11380step2 raw11380step2Labels raw11380step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw11381 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11381step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11381step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11381step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11381step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11381step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11381step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11381step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11381 raw11381Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw11381 raw11381Labels = mixedMoment B raw11381step0 raw11381step0Labels := by
      have hz : ∀ j, raw11381 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11381step0 = (fun i j => raw11381 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11381step0 raw11381; decide +kernel
      have hl : raw11381step0Labels = raw11381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11381 raw11381Labels permutation434 hz
    mixedMoment B raw11381step0 raw11381step0Labels = mixedMoment B raw11381step1 raw11381step1Labels := by
      have hz : ∀ j, raw11381step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11381step1 = (fun i j => raw11381step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11381step1 raw11381step0; decide +kernel
      have hl : raw11381step1Labels = raw11381step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11381step0 raw11381step0Labels permutation56 hz
    mixedMoment B raw11381step1 raw11381step1Labels = mixedMoment B raw11381step2 raw11381step2Labels := by
      have ha : raw11381step2 = (fun i j => raw11381step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11381step2 raw11381step1; decide +kernel
      have hl : raw11381step2Labels = raw11381step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11381step1 raw11381step1Labels permutation10 permutation4
    mixedMoment B raw11381step2 raw11381step2Labels = mixedMoment B raw11381step3 raw11381step3Labels := by
      have ha : raw11381step3 = -raw11381step2 := by apply Matrix.ext; change ∀ i j, raw11381step3 i j = -(raw11381step2 i j); unfold raw11381step3 raw11381step2; decide +kernel
      have hl : raw11381step3Labels = raw11381step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11381step3 raw11381step3Labels = mixedMoment B raw11381step4 raw11381step4Labels := by
      have ha : raw11381step4 = raw11381step3 := by apply Matrix.ext; unfold raw11381step4 raw11381step3; decide +kernel
      have hl : raw11381step3Labels = labelEmbedding7 ∘ raw11381step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11381step3 raw11381step3Labels raw11381step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw11382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11382step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11382step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11382 raw11382Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw11382 raw11382Labels = mixedMoment B raw11382step0 raw11382step0Labels := by
      have hz : ∀ j, raw11382 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11382step0 = (fun i j => raw11382 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11382step0 raw11382; decide +kernel
      have hl : raw11382step0Labels = raw11382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11382 raw11382Labels permutation434 hz
    mixedMoment B raw11382step0 raw11382step0Labels = mixedMoment B raw11382step1 raw11382step1Labels := by
      have hz : ∀ j, raw11382step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11382step1 = (fun i j => raw11382step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11382step1 raw11382step0; decide +kernel
      have hl : raw11382step1Labels = raw11382step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11382step0 raw11382step0Labels permutation80 hz
    mixedMoment B raw11382step1 raw11382step1Labels = mixedMoment B raw11382step2 raw11382step2Labels := by
      have ha : raw11382step2 = (fun i j => raw11382step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11382step2 raw11382step1; decide +kernel
      have hl : raw11382step2Labels = raw11382step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11382step1 raw11382step1Labels permutation8 permutation6
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw11383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11383 raw11383Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw11383 raw11383Labels = mixedMoment B raw11383step0 raw11383step0Labels := by
      have hz : ∀ j, raw11383 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11383step0 = (fun i j => raw11383 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11383step0 raw11383; decide +kernel
      have hl : raw11383step0Labels = raw11383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11383 raw11383Labels permutation434 hz
    mixedMoment B raw11383step0 raw11383step0Labels = mixedMoment B raw11383step1 raw11383step1Labels := by
      have ha : raw11383step1 = (fun i j => raw11383step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11383step1 raw11383step0; decide +kernel
      have hl : raw11383step1Labels = raw11383step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11383step0 raw11383step0Labels permutation32 permutation6
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw11384 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11384step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11384 raw11384Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw11384 raw11384Labels = mixedMoment B raw11384step0 raw11384step0Labels := by
      have hz : ∀ j, raw11384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11384step0 = (fun i j => raw11384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11384step0 raw11384; decide +kernel
      have hl : raw11384step0Labels = raw11384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11384 raw11384Labels permutation434 hz
    mixedMoment B raw11384step0 raw11384step0Labels = mixedMoment B raw11384step1 raw11384step1Labels := by
      have hz : ∀ j, raw11384step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11384step1 = (fun i j => raw11384step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11384step1 raw11384step0; decide +kernel
      have hl : raw11384step1Labels = raw11384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11384step0 raw11384step0Labels permutation56 hz
    mixedMoment B raw11384step1 raw11384step1Labels = mixedMoment B raw11384step2 raw11384step2Labels := by
      have ha : raw11384step2 = (fun i j => raw11384step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11384step2 raw11384step1; decide +kernel
      have hl : raw11384step2Labels = raw11384step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11384step1 raw11384step1Labels permutation8 permutation6
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw11385 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11385 raw11385Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw11385 raw11385Labels = mixedMoment B raw11385step0 raw11385step0Labels := by
      have ha : raw11385step0 = (fun i j => raw11385 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11385step0 raw11385; decide +kernel
      have hl : raw11385step0Labels = raw11385Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11385 raw11385Labels permutation200 permutation6
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw11386 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw11386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11386 raw11386Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw11386 raw11386Labels = mixedMoment B raw11386step0 raw11386step0Labels := by
      have hz : ∀ j, raw11386 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11386step0 = (fun i j => raw11386 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11386step0 raw11386; decide +kernel
      have hl : raw11386step0Labels = raw11386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11386 raw11386Labels permutation434 hz
    mixedMoment B raw11386step0 raw11386step0Labels = mixedMoment B raw11386step1 raw11386step1Labels := by
      have ha : raw11386step1 = (fun i j => raw11386step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11386step1 raw11386step0; decide +kernel
      have hl : raw11386step1Labels = raw11386step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11386step0 raw11386step0Labels permutation32 permutation6
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw11387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11387 raw11387Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw11387 raw11387Labels = mixedMoment B raw11387step0 raw11387step0Labels := by
      have hz : ∀ j, raw11387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11387step0 = (fun i j => raw11387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11387step0 raw11387; decide +kernel
      have hl : raw11387step0Labels = raw11387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11387 raw11387Labels permutation434 hz
    mixedMoment B raw11387step0 raw11387step0Labels = mixedMoment B raw11387step1 raw11387step1Labels := by
      have ha : raw11387step1 = (fun i j => raw11387step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11387step1 raw11387step0; decide +kernel
      have hl : raw11387step1Labels = raw11387step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11387step0 raw11387step0Labels permutation32 permutation6
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw11388 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11388step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11388 raw11388Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw11388 raw11388Labels = mixedMoment B raw11388step0 raw11388step0Labels := by
      have hz : ∀ j, raw11388 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11388step0 = (fun i j => raw11388 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11388step0 raw11388; decide +kernel
      have hl : raw11388step0Labels = raw11388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11388 raw11388Labels permutation434 hz
    mixedMoment B raw11388step0 raw11388step0Labels = mixedMoment B raw11388step1 raw11388step1Labels := by
      have hz : ∀ j, raw11388step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11388step1 = (fun i j => raw11388step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11388step1 raw11388step0; decide +kernel
      have hl : raw11388step1Labels = raw11388step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11388step0 raw11388step0Labels permutation56 hz
    mixedMoment B raw11388step1 raw11388step1Labels = mixedMoment B raw11388step2 raw11388step2Labels := by
      have ha : raw11388step2 = (fun i j => raw11388step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11388step2 raw11388step1; decide +kernel
      have hl : raw11388step2Labels = raw11388step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11388step1 raw11388step1Labels permutation8 permutation6
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw11389 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11389Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11389step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11389step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11389step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11389step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11389step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11389 raw11389Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw11389 raw11389Labels = mixedMoment B raw11389step0 raw11389step0Labels := by
      have hz : ∀ j, raw11389 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11389step0 = (fun i j => raw11389 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11389step0 raw11389; decide +kernel
      have hl : raw11389step0Labels = raw11389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11389 raw11389Labels permutation434 hz
    mixedMoment B raw11389step0 raw11389step0Labels = mixedMoment B raw11389step1 raw11389step1Labels := by
      have hz : ∀ j, raw11389step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11389step1 = (fun i j => raw11389step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11389step1 raw11389step0; decide +kernel
      have hl : raw11389step1Labels = raw11389step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11389step0 raw11389step0Labels permutation80 hz
    mixedMoment B raw11389step1 raw11389step1Labels = mixedMoment B raw11389step2 raw11389step2Labels := by
      have ha : raw11389step2 = (fun i j => raw11389step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11389step2 raw11389step1; decide +kernel
      have hl : raw11389step2Labels = raw11389step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11389step1 raw11389step1Labels permutation8 permutation7
    mixedMoment B raw11389step2 raw11389step2Labels = mixedMoment B raw11389step3 raw11389step3Labels := by
      have ha : raw11389step3 = raw11389step2 := by apply Matrix.ext; unfold raw11389step3 raw11389step2; decide +kernel
      have hl : raw11389step2Labels = labelEmbedding1 ∘ raw11389step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11389step2 raw11389step2Labels raw11389step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw11390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11390Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11390step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11390step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11390step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11390step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11390step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11390 raw11390Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw11390 raw11390Labels = mixedMoment B raw11390step0 raw11390step0Labels := by
      have hz : ∀ j, raw11390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11390step0 = (fun i j => raw11390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11390step0 raw11390; decide +kernel
      have hl : raw11390step0Labels = raw11390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11390 raw11390Labels permutation434 hz
    mixedMoment B raw11390step0 raw11390step0Labels = mixedMoment B raw11390step1 raw11390step1Labels := by
      have ha : raw11390step1 = (fun i j => raw11390step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11390step1 raw11390step0; decide +kernel
      have hl : raw11390step1Labels = raw11390step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11390step0 raw11390step0Labels permutation48 permutation5
    mixedMoment B raw11390step1 raw11390step1Labels = mixedMoment B raw11390step2 raw11390step2Labels := by
      have ha : raw11390step2 = -raw11390step1 := by apply Matrix.ext; change ∀ i j, raw11390step2 i j = -(raw11390step1 i j); unfold raw11390step2 raw11390step1; decide +kernel
      have hl : raw11390step2Labels = raw11390step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11390step2 raw11390step2Labels = mixedMoment B raw11390step3 raw11390step3Labels := by
      have ha : raw11390step3 = raw11390step2 := by apply Matrix.ext; unfold raw11390step3 raw11390step2; decide +kernel
      have hl : raw11390step2Labels = labelEmbedding1 ∘ raw11390step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11390step2 raw11390step2Labels raw11390step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw11391 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11391Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11391step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11391step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11391step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11391step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11391step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11391step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11391 raw11391Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw11391 raw11391Labels = mixedMoment B raw11391step0 raw11391step0Labels := by
      have hz : ∀ j, raw11391 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11391step0 = (fun i j => raw11391 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11391step0 raw11391; decide +kernel
      have hl : raw11391step0Labels = raw11391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11391 raw11391Labels permutation434 hz
    mixedMoment B raw11391step0 raw11391step0Labels = mixedMoment B raw11391step1 raw11391step1Labels := by
      have hz : ∀ j, raw11391step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11391step1 = (fun i j => raw11391step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11391step1 raw11391step0; decide +kernel
      have hl : raw11391step1Labels = raw11391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11391step0 raw11391step0Labels permutation56 hz
    mixedMoment B raw11391step1 raw11391step1Labels = mixedMoment B raw11391step2 raw11391step2Labels := by
      have ha : raw11391step2 = (fun i j => raw11391step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11391step2 raw11391step1; decide +kernel
      have hl : raw11391step2Labels = raw11391step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11391step1 raw11391step1Labels permutation8 permutation7
    mixedMoment B raw11391step2 raw11391step2Labels = mixedMoment B raw11391step3 raw11391step3Labels := by
      have ha : raw11391step3 = raw11391step2 := by apply Matrix.ext; unfold raw11391step3 raw11391step2; decide +kernel
      have hl : raw11391step2Labels = labelEmbedding1 ∘ raw11391step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11391step2 raw11391step2Labels raw11391step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
