import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16512 raw16512Labels = mixedMoment B node2098 node2098Labels := by
  calc
    mixedMoment B raw16512 raw16512Labels = mixedMoment B raw16512step0 raw16512step0Labels := by
      have ha : raw16512step0 = (fun i j => raw16512 (permutation226 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16512step0 raw16512; decide +kernel
      have hl : raw16512step0Labels = raw16512Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16512 raw16512Labels permutation226 permutation5
    mixedMoment B raw16512step0 raw16512step0Labels = mixedMoment B raw16512step1 raw16512step1Labels := by
      have ha : raw16512step1 = -raw16512step0 := by apply Matrix.ext; change ∀ i j, raw16512step1 i j = -(raw16512step0 i j); unfold raw16512step1 raw16512step0; decide +kernel
      have hl : raw16512step1Labels = raw16512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16512step1 raw16512step1Labels = mixedMoment B raw16512step2 raw16512step2Labels := by
      have ha : raw16512step2 = raw16512step1 := by apply Matrix.ext; unfold raw16512step2 raw16512step1; decide +kernel
      have hl : raw16512step1Labels = labelEmbedding1 ∘ raw16512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16512step1 raw16512step1Labels raw16512step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2098 node2098Labels := by rfl

def raw16513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16513step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16513step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16513 raw16513Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw16513 raw16513Labels = mixedMoment B raw16513step0 raw16513step0Labels := by
      have ha : raw16513step0 = (fun i j => raw16513 (permutation306 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16513step0 raw16513; decide +kernel
      have hl : raw16513step0Labels = raw16513Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16513 raw16513Labels permutation306 permutation7
    mixedMoment B raw16513step0 raw16513step0Labels = mixedMoment B raw16513step1 raw16513step1Labels := by
      have ha : raw16513step1 = -raw16513step0 := by apply Matrix.ext; change ∀ i j, raw16513step1 i j = -(raw16513step0 i j); unfold raw16513step1 raw16513step0; decide +kernel
      have hl : raw16513step1Labels = raw16513step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16513step1 raw16513step1Labels = mixedMoment B raw16513step2 raw16513step2Labels := by
      have ha : raw16513step2 = raw16513step1 := by apply Matrix.ext; unfold raw16513step2 raw16513step1; decide +kernel
      have hl : raw16513step1Labels = labelEmbedding1 ∘ raw16513step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16513step1 raw16513step1Labels raw16513step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw16514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16514step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16514 raw16514Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw16514 raw16514Labels = mixedMoment B raw16514step0 raw16514step0Labels := by
      have ha : raw16514step0 = (fun i j => raw16514 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16514step0 raw16514; decide +kernel
      have hl : raw16514step0Labels = raw16514Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16514 raw16514Labels permutation234 permutation5
    mixedMoment B raw16514step0 raw16514step0Labels = mixedMoment B raw16514step1 raw16514step1Labels := by
      have ha : raw16514step1 = -raw16514step0 := by apply Matrix.ext; change ∀ i j, raw16514step1 i j = -(raw16514step0 i j); unfold raw16514step1 raw16514step0; decide +kernel
      have hl : raw16514step1Labels = raw16514step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16514step1 raw16514step1Labels = mixedMoment B raw16514step2 raw16514step2Labels := by
      have ha : raw16514step2 = raw16514step1 := by apply Matrix.ext; unfold raw16514step2 raw16514step1; decide +kernel
      have hl : raw16514step1Labels = labelEmbedding1 ∘ raw16514step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16514step1 raw16514step1Labels raw16514step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw16515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16515step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16515step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16515step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16515 raw16515Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw16515 raw16515Labels = mixedMoment B raw16515step0 raw16515step0Labels := by
      have ha : raw16515step0 = (fun i j => raw16515 (permutation226 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16515step0 raw16515; decide +kernel
      have hl : raw16515step0Labels = raw16515Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16515 raw16515Labels permutation226 permutation5
    mixedMoment B raw16515step0 raw16515step0Labels = mixedMoment B raw16515step1 raw16515step1Labels := by
      have ha : raw16515step1 = -raw16515step0 := by apply Matrix.ext; change ∀ i j, raw16515step1 i j = -(raw16515step0 i j); unfold raw16515step1 raw16515step0; decide +kernel
      have hl : raw16515step1Labels = raw16515step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16515step1 raw16515step1Labels = mixedMoment B raw16515step2 raw16515step2Labels := by
      have ha : raw16515step2 = raw16515step1 := by apply Matrix.ext; unfold raw16515step2 raw16515step1; decide +kernel
      have hl : raw16515step1Labels = labelEmbedding1 ∘ raw16515step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16515step1 raw16515step1Labels raw16515step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3730 node3730Labels := by rfl

def raw16516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16516step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16516 raw16516Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw16516 raw16516Labels = mixedMoment B raw16516step0 raw16516step0Labels := by
      have ha : raw16516step0 = (fun i j => raw16516 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16516step0 raw16516; decide +kernel
      have hl : raw16516step0Labels = raw16516Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16516 raw16516Labels permutation241 permutation5
    mixedMoment B raw16516step0 raw16516step0Labels = mixedMoment B raw16516step1 raw16516step1Labels := by
      have ha : raw16516step1 = -raw16516step0 := by apply Matrix.ext; change ∀ i j, raw16516step1 i j = -(raw16516step0 i j); unfold raw16516step1 raw16516step0; decide +kernel
      have hl : raw16516step1Labels = raw16516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16516step1 raw16516step1Labels = mixedMoment B raw16516step2 raw16516step2Labels := by
      have ha : raw16516step2 = raw16516step1 := by apply Matrix.ext; unfold raw16516step2 raw16516step1; decide +kernel
      have hl : raw16516step1Labels = labelEmbedding1 ∘ raw16516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16516step1 raw16516step1Labels raw16516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw16517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16517 raw16517Labels = mixedMoment B node2102 node2102Labels := by
  calc
    mixedMoment B raw16517 raw16517Labels = mixedMoment B raw16517step0 raw16517step0Labels := by
      have hz : ∀ j, raw16517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16517step0 = (fun i j => raw16517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16517step0 raw16517; decide +kernel
      have hl : raw16517step0Labels = raw16517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16517 raw16517Labels permutation346 hz
    mixedMoment B raw16517step0 raw16517step0Labels = mixedMoment B raw16517step1 raw16517step1Labels := by
      have ha : raw16517step1 = (fun i j => raw16517step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16517step1 raw16517step0; decide +kernel
      have hl : raw16517step1Labels = raw16517step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16517step0 raw16517step0Labels permutation45 permutation5
    mixedMoment B raw16517step1 raw16517step1Labels = mixedMoment B raw16517step2 raw16517step2Labels := by
      have ha : raw16517step2 = -raw16517step1 := by apply Matrix.ext; change ∀ i j, raw16517step2 i j = -(raw16517step1 i j); unfold raw16517step2 raw16517step1; decide +kernel
      have hl : raw16517step2Labels = raw16517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16517step2 raw16517step2Labels = mixedMoment B raw16517step3 raw16517step3Labels := by
      have ha : raw16517step3 = raw16517step2 := by apply Matrix.ext; unfold raw16517step3 raw16517step2; decide +kernel
      have hl : raw16517step2Labels = labelEmbedding1 ∘ raw16517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16517step2 raw16517step2Labels raw16517step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2102 node2102Labels := by rfl

def raw16518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw16518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16518step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16518step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16518 raw16518Labels = mixedMoment B node3868 node3868Labels := by
  calc
    mixedMoment B raw16518 raw16518Labels = mixedMoment B raw16518step0 raw16518step0Labels := by
      have hz : ∀ j, raw16518 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16518step0 = (fun i j => raw16518 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16518step0 raw16518; decide +kernel
      have hl : raw16518step0Labels = raw16518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16518 raw16518Labels permutation346 hz
    mixedMoment B raw16518step0 raw16518step0Labels = mixedMoment B raw16518step1 raw16518step1Labels := by
      have ha : raw16518step1 = (fun i j => raw16518step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16518step1 raw16518step0; decide +kernel
      have hl : raw16518step1Labels = raw16518step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16518step0 raw16518step0Labels permutation45 permutation5
    mixedMoment B raw16518step1 raw16518step1Labels = mixedMoment B raw16518step2 raw16518step2Labels := by
      have ha : raw16518step2 = -raw16518step1 := by apply Matrix.ext; change ∀ i j, raw16518step2 i j = -(raw16518step1 i j); unfold raw16518step2 raw16518step1; decide +kernel
      have hl : raw16518step2Labels = raw16518step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16518step2 raw16518step2Labels = mixedMoment B raw16518step3 raw16518step3Labels := by
      have ha : raw16518step3 = raw16518step2 := by apply Matrix.ext; unfold raw16518step3 raw16518step2; decide +kernel
      have hl : raw16518step2Labels = labelEmbedding1 ∘ raw16518step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16518step2 raw16518step2Labels raw16518step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3868 node3868Labels := by rfl

def raw16519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16519step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16519step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16519 raw16519Labels = mixedMoment B node3785 node3785Labels := by
  calc
    mixedMoment B raw16519 raw16519Labels = mixedMoment B raw16519step0 raw16519step0Labels := by
      have ha : raw16519step0 = (fun i j => raw16519 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16519step0 raw16519; decide +kernel
      have hl : raw16519step0Labels = raw16519Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16519 raw16519Labels permutation189 permutation5
    mixedMoment B raw16519step0 raw16519step0Labels = mixedMoment B raw16519step1 raw16519step1Labels := by
      have ha : raw16519step1 = -raw16519step0 := by apply Matrix.ext; change ∀ i j, raw16519step1 i j = -(raw16519step0 i j); unfold raw16519step1 raw16519step0; decide +kernel
      have hl : raw16519step1Labels = raw16519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16519step1 raw16519step1Labels = mixedMoment B raw16519step2 raw16519step2Labels := by
      have ha : raw16519step2 = raw16519step1 := by apply Matrix.ext; unfold raw16519step2 raw16519step1; decide +kernel
      have hl : raw16519step1Labels = labelEmbedding1 ∘ raw16519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16519step1 raw16519step1Labels raw16519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3785 node3785Labels := by rfl

def raw16520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16520step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16520step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16520 raw16520Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw16520 raw16520Labels = mixedMoment B raw16520step0 raw16520step0Labels := by
      have hz : ∀ j, raw16520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16520step0 = (fun i j => raw16520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16520step0 raw16520; decide +kernel
      have hl : raw16520step0Labels = raw16520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16520 raw16520Labels permutation346 hz
    mixedMoment B raw16520step0 raw16520step0Labels = mixedMoment B raw16520step1 raw16520step1Labels := by
      have ha : raw16520step1 = (fun i j => raw16520step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16520step1 raw16520step0; decide +kernel
      have hl : raw16520step1Labels = raw16520step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16520step0 raw16520step0Labels permutation45 permutation5
    mixedMoment B raw16520step1 raw16520step1Labels = mixedMoment B raw16520step2 raw16520step2Labels := by
      have ha : raw16520step2 = -raw16520step1 := by apply Matrix.ext; change ∀ i j, raw16520step2 i j = -(raw16520step1 i j); unfold raw16520step2 raw16520step1; decide +kernel
      have hl : raw16520step2Labels = raw16520step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16520step2 raw16520step2Labels = mixedMoment B raw16520step3 raw16520step3Labels := by
      have ha : raw16520step3 = raw16520step2 := by apply Matrix.ext; unfold raw16520step3 raw16520step2; decide +kernel
      have hl : raw16520step2Labels = labelEmbedding1 ∘ raw16520step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16520step2 raw16520step2Labels raw16520step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3733 node3733Labels := by rfl

def raw16521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16521step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16521step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16521step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16521 raw16521Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw16521 raw16521Labels = mixedMoment B raw16521step0 raw16521step0Labels := by
      have hz : ∀ j, raw16521 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16521step0 = (fun i j => raw16521 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16521step0 raw16521; decide +kernel
      have hl : raw16521step0Labels = raw16521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16521 raw16521Labels permutation346 hz
    mixedMoment B raw16521step0 raw16521step0Labels = mixedMoment B raw16521step1 raw16521step1Labels := by
      have ha : raw16521step1 = (fun i j => raw16521step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16521step1 raw16521step0; decide +kernel
      have hl : raw16521step1Labels = raw16521step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16521step0 raw16521step0Labels permutation48 permutation5
    mixedMoment B raw16521step1 raw16521step1Labels = mixedMoment B raw16521step2 raw16521step2Labels := by
      have ha : raw16521step2 = -raw16521step1 := by apply Matrix.ext; change ∀ i j, raw16521step2 i j = -(raw16521step1 i j); unfold raw16521step2 raw16521step1; decide +kernel
      have hl : raw16521step2Labels = raw16521step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16521step2 raw16521step2Labels = mixedMoment B raw16521step3 raw16521step3Labels := by
      have ha : raw16521step3 = raw16521step2 := by apply Matrix.ext; unfold raw16521step3 raw16521step2; decide +kernel
      have hl : raw16521step2Labels = labelEmbedding1 ∘ raw16521step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16521step2 raw16521step2Labels raw16521step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw16522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16522step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16522step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16522step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16522step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16522step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16522 raw16522Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw16522 raw16522Labels = mixedMoment B raw16522step0 raw16522step0Labels := by
      have hz : ∀ j, raw16522 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16522step0 = (fun i j => raw16522 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16522step0 raw16522; decide +kernel
      have hl : raw16522step0Labels = raw16522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16522 raw16522Labels permutation346 hz
    mixedMoment B raw16522step0 raw16522step0Labels = mixedMoment B raw16522step1 raw16522step1Labels := by
      have ha : raw16522step1 = (fun i j => raw16522step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16522step1 raw16522step0; decide +kernel
      have hl : raw16522step1Labels = raw16522step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16522step0 raw16522step0Labels permutation44 permutation5
    mixedMoment B raw16522step1 raw16522step1Labels = mixedMoment B raw16522step2 raw16522step2Labels := by
      have ha : raw16522step2 = -raw16522step1 := by apply Matrix.ext; change ∀ i j, raw16522step2 i j = -(raw16522step1 i j); unfold raw16522step2 raw16522step1; decide +kernel
      have hl : raw16522step2Labels = raw16522step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16522step2 raw16522step2Labels = mixedMoment B raw16522step3 raw16522step3Labels := by
      have ha : raw16522step3 = raw16522step2 := by apply Matrix.ext; unfold raw16522step3 raw16522step2; decide +kernel
      have hl : raw16522step2Labels = labelEmbedding1 ∘ raw16522step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16522step2 raw16522step2Labels raw16522step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw16523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16523step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16523step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16523 raw16523Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw16523 raw16523Labels = mixedMoment B raw16523step0 raw16523step0Labels := by
      have hz : ∀ j, raw16523 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16523step0 = (fun i j => raw16523 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16523step0 raw16523; decide +kernel
      have hl : raw16523step0Labels = raw16523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16523 raw16523Labels permutation346 hz
    mixedMoment B raw16523step0 raw16523step0Labels = mixedMoment B raw16523step1 raw16523step1Labels := by
      have ha : raw16523step1 = (fun i j => raw16523step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16523step1 raw16523step0; decide +kernel
      have hl : raw16523step1Labels = raw16523step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16523step0 raw16523step0Labels permutation123 permutation7
    mixedMoment B raw16523step1 raw16523step1Labels = mixedMoment B raw16523step2 raw16523step2Labels := by
      have ha : raw16523step2 = raw16523step1 := by apply Matrix.ext; unfold raw16523step2 raw16523step1; decide +kernel
      have hl : raw16523step1Labels = labelEmbedding1 ∘ raw16523step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16523step1 raw16523step1Labels raw16523step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw16524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16524 raw16524Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw16524 raw16524Labels = mixedMoment B raw16524step0 raw16524step0Labels := by
      have ha : raw16524step0 = (fun i j => raw16524 (permutation581 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16524step0 raw16524; decide +kernel
      have hl : raw16524step0Labels = raw16524Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16524 raw16524Labels permutation581 permutation7
    mixedMoment B raw16524step0 raw16524step0Labels = mixedMoment B raw16524step1 raw16524step1Labels := by
      have ha : raw16524step1 = raw16524step0 := by apply Matrix.ext; unfold raw16524step1 raw16524step0; decide +kernel
      have hl : raw16524step0Labels = labelEmbedding1 ∘ raw16524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16524step0 raw16524step0Labels raw16524step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw16525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16525step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16525step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16525 raw16525Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw16525 raw16525Labels = mixedMoment B raw16525step0 raw16525step0Labels := by
      have hz : ∀ j, raw16525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16525step0 = (fun i j => raw16525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16525step0 raw16525; decide +kernel
      have hl : raw16525step0Labels = raw16525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16525 raw16525Labels permutation346 hz
    mixedMoment B raw16525step0 raw16525step0Labels = mixedMoment B raw16525step1 raw16525step1Labels := by
      have ha : raw16525step1 = (fun i j => raw16525step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16525step1 raw16525step0; decide +kernel
      have hl : raw16525step1Labels = raw16525step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16525step0 raw16525step0Labels permutation123 permutation7
    mixedMoment B raw16525step1 raw16525step1Labels = mixedMoment B raw16525step2 raw16525step2Labels := by
      have ha : raw16525step2 = raw16525step1 := by apply Matrix.ext; unfold raw16525step2 raw16525step1; decide +kernel
      have hl : raw16525step1Labels = labelEmbedding1 ∘ raw16525step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16525step1 raw16525step1Labels raw16525step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

def raw16526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16526 raw16526Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw16526 raw16526Labels = mixedMoment B raw16526step0 raw16526step0Labels := by
      have hz : ∀ j, raw16526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16526step0 = (fun i j => raw16526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16526step0 raw16526; decide +kernel
      have hl : raw16526step0Labels = raw16526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16526 raw16526Labels permutation346 hz
    mixedMoment B raw16526step0 raw16526step0Labels = mixedMoment B raw16526step1 raw16526step1Labels := by
      have ha : raw16526step1 = (fun i j => raw16526step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16526step1 raw16526step0; decide +kernel
      have hl : raw16526step1Labels = raw16526step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16526step0 raw16526step0Labels permutation123 permutation7
    mixedMoment B raw16526step1 raw16526step1Labels = mixedMoment B raw16526step2 raw16526step2Labels := by
      have ha : raw16526step2 = raw16526step1 := by apply Matrix.ext; unfold raw16526step2 raw16526step1; decide +kernel
      have hl : raw16526step1Labels = labelEmbedding1 ∘ raw16526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16526step1 raw16526step1Labels raw16526step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw16527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16527step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw16527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16527step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16527step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16527 raw16527Labels = mixedMoment B node2099 node2099Labels := by
  calc
    mixedMoment B raw16527 raw16527Labels = mixedMoment B raw16527step0 raw16527step0Labels := by
      have hz : ∀ j, raw16527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16527step0 = (fun i j => raw16527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16527step0 raw16527; decide +kernel
      have hl : raw16527step0Labels = raw16527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16527 raw16527Labels permutation346 hz
    mixedMoment B raw16527step0 raw16527step0Labels = mixedMoment B raw16527step1 raw16527step1Labels := by
      have ha : raw16527step1 = (fun i j => raw16527step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16527step1 raw16527step0; decide +kernel
      have hl : raw16527step1Labels = raw16527step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16527step0 raw16527step0Labels permutation44 permutation5
    mixedMoment B raw16527step1 raw16527step1Labels = mixedMoment B raw16527step2 raw16527step2Labels := by
      have ha : raw16527step2 = -raw16527step1 := by apply Matrix.ext; change ∀ i j, raw16527step2 i j = -(raw16527step1 i j); unfold raw16527step2 raw16527step1; decide +kernel
      have hl : raw16527step2Labels = raw16527step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16527step2 raw16527step2Labels = mixedMoment B raw16527step3 raw16527step3Labels := by
      have ha : raw16527step3 = raw16527step2 := by apply Matrix.ext; unfold raw16527step3 raw16527step2; decide +kernel
      have hl : raw16527step2Labels = labelEmbedding1 ∘ raw16527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16527step2 raw16527step2Labels raw16527step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2099 node2099Labels := by rfl

def raw16528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16528step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16528 raw16528Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw16528 raw16528Labels = mixedMoment B raw16528step0 raw16528step0Labels := by
      have hz : ∀ j, raw16528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16528step0 = (fun i j => raw16528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16528step0 raw16528; decide +kernel
      have hl : raw16528step0Labels = raw16528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16528 raw16528Labels permutation346 hz
    mixedMoment B raw16528step0 raw16528step0Labels = mixedMoment B raw16528step1 raw16528step1Labels := by
      have ha : raw16528step1 = (fun i j => raw16528step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16528step1 raw16528step0; decide +kernel
      have hl : raw16528step1Labels = raw16528step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16528step0 raw16528step0Labels permutation143 permutation5
    mixedMoment B raw16528step1 raw16528step1Labels = mixedMoment B raw16528step2 raw16528step2Labels := by
      have ha : raw16528step2 = raw16528step1 := by apply Matrix.ext; unfold raw16528step2 raw16528step1; decide +kernel
      have hl : raw16528step1Labels = labelEmbedding1 ∘ raw16528step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16528step1 raw16528step1Labels raw16528step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw16529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16529 raw16529Labels = mixedMoment B node3501 node3501Labels := by
  calc
    mixedMoment B raw16529 raw16529Labels = mixedMoment B raw16529step0 raw16529step0Labels := by
      have ha : raw16529step0 = (fun i j => raw16529 (permutation654 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16529step0 raw16529; decide +kernel
      have hl : raw16529step0Labels = raw16529Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16529 raw16529Labels permutation654 permutation5
    mixedMoment B raw16529step0 raw16529step0Labels = mixedMoment B raw16529step1 raw16529step1Labels := by
      have ha : raw16529step1 = raw16529step0 := by apply Matrix.ext; unfold raw16529step1 raw16529step0; decide +kernel
      have hl : raw16529step0Labels = labelEmbedding1 ∘ raw16529step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16529step0 raw16529step0Labels raw16529step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3501 node3501Labels := by rfl

def raw16530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16530step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16530 raw16530Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw16530 raw16530Labels = mixedMoment B raw16530step0 raw16530step0Labels := by
      have hz : ∀ j, raw16530 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16530step0 = (fun i j => raw16530 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16530step0 raw16530; decide +kernel
      have hl : raw16530step0Labels = raw16530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16530 raw16530Labels permutation346 hz
    mixedMoment B raw16530step0 raw16530step0Labels = mixedMoment B raw16530step1 raw16530step1Labels := by
      have ha : raw16530step1 = (fun i j => raw16530step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16530step1 raw16530step0; decide +kernel
      have hl : raw16530step1Labels = raw16530step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16530step0 raw16530step0Labels permutation137 permutation5
    mixedMoment B raw16530step1 raw16530step1Labels = mixedMoment B raw16530step2 raw16530step2Labels := by
      have ha : raw16530step2 = raw16530step1 := by apply Matrix.ext; unfold raw16530step2 raw16530step1; decide +kernel
      have hl : raw16530step1Labels = labelEmbedding1 ∘ raw16530step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16530step1 raw16530step1Labels raw16530step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw16531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16531step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16531 raw16531Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw16531 raw16531Labels = mixedMoment B raw16531step0 raw16531step0Labels := by
      have hz : ∀ j, raw16531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16531step0 = (fun i j => raw16531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16531step0 raw16531; decide +kernel
      have hl : raw16531step0Labels = raw16531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16531 raw16531Labels permutation346 hz
    mixedMoment B raw16531step0 raw16531step0Labels = mixedMoment B raw16531step1 raw16531step1Labels := by
      have ha : raw16531step1 = (fun i j => raw16531step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16531step1 raw16531step0; decide +kernel
      have hl : raw16531step1Labels = raw16531step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16531step0 raw16531step0Labels permutation143 permutation5
    mixedMoment B raw16531step1 raw16531step1Labels = mixedMoment B raw16531step2 raw16531step2Labels := by
      have ha : raw16531step2 = raw16531step1 := by apply Matrix.ext; unfold raw16531step2 raw16531step1; decide +kernel
      have hl : raw16531step1Labels = labelEmbedding1 ∘ raw16531step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16531step1 raw16531step1Labels raw16531step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3506 node3506Labels := by rfl

def raw16532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16532 raw16532Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw16532 raw16532Labels = mixedMoment B raw16532step0 raw16532step0Labels := by
      have hz : ∀ j, raw16532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16532step0 = (fun i j => raw16532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16532step0 raw16532; decide +kernel
      have hl : raw16532step0Labels = raw16532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16532 raw16532Labels permutation346 hz
    mixedMoment B raw16532step0 raw16532step0Labels = mixedMoment B raw16532step1 raw16532step1Labels := by
      have ha : raw16532step1 = (fun i j => raw16532step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16532step1 raw16532step0; decide +kernel
      have hl : raw16532step1Labels = raw16532step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16532step0 raw16532step0Labels permutation151 permutation2
    mixedMoment B raw16532step1 raw16532step1Labels = mixedMoment B raw16532step2 raw16532step2Labels := by
      have ha : raw16532step2 = -raw16532step1 := by apply Matrix.ext; change ∀ i j, raw16532step2 i j = -(raw16532step1 i j); unfold raw16532step2 raw16532step1; decide +kernel
      have hl : raw16532step2Labels = raw16532step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw16533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16533 raw16533Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw16533 raw16533Labels = mixedMoment B raw16533step0 raw16533step0Labels := by
      have hz : ∀ j, raw16533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16533step0 = (fun i j => raw16533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16533step0 raw16533; decide +kernel
      have hl : raw16533step0Labels = raw16533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16533 raw16533Labels permutation346 hz
    mixedMoment B raw16533step0 raw16533step0Labels = mixedMoment B raw16533step1 raw16533step1Labels := by
      have ha : raw16533step1 = (fun i j => raw16533step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16533step1 raw16533step0; decide +kernel
      have hl : raw16533step1Labels = raw16533step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16533step0 raw16533step0Labels permutation49 permutation4
    mixedMoment B raw16533step1 raw16533step1Labels = mixedMoment B raw16533step2 raw16533step2Labels := by
      have ha : raw16533step2 = -raw16533step1 := by apply Matrix.ext; change ∀ i j, raw16533step2 i j = -(raw16533step1 i j); unfold raw16533step2 raw16533step1; decide +kernel
      have hl : raw16533step2Labels = raw16533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw16534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16534 raw16534Labels = mixedMoment B node3171 node3171Labels := by
  calc
    mixedMoment B raw16534 raw16534Labels = mixedMoment B raw16534step0 raw16534step0Labels := by
      have ha : raw16534step0 = (fun i j => raw16534 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16534step0 raw16534; decide +kernel
      have hl : raw16534step0Labels = raw16534Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16534 raw16534Labels permutation158 permutation2
    _ = mixedMoment B node3171 node3171Labels := by rfl

def raw16535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16535 raw16535Labels = mixedMoment B node3181 node3181Labels := by
  calc
    mixedMoment B raw16535 raw16535Labels = mixedMoment B raw16535step0 raw16535step0Labels := by
      have hz : ∀ j, raw16535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16535step0 = (fun i j => raw16535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16535step0 raw16535; decide +kernel
      have hl : raw16535step0Labels = raw16535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16535 raw16535Labels permutation346 hz
    _ = mixedMoment B node3181 node3181Labels := by rfl

def raw16536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16536 raw16536Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw16536 raw16536Labels = mixedMoment B raw16536step0 raw16536step0Labels := by
      have hz : ∀ j, raw16536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16536step0 = (fun i j => raw16536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16536step0 raw16536; decide +kernel
      have hl : raw16536step0Labels = raw16536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16536 raw16536Labels permutation346 hz
    mixedMoment B raw16536step0 raw16536step0Labels = mixedMoment B raw16536step1 raw16536step1Labels := by
      have ha : raw16536step1 = (fun i j => raw16536step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16536step1 raw16536step0; decide +kernel
      have hl : raw16536step1Labels = raw16536step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16536step0 raw16536step0Labels permutation33 permutation2
    _ = mixedMoment B node3174 node3174Labels := by rfl

def raw16537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw16537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16537step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw16537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16537 raw16537Labels = mixedMoment B node2866 node2866Labels := by
  calc
    mixedMoment B raw16537 raw16537Labels = mixedMoment B raw16537step0 raw16537step0Labels := by
      have hz : ∀ j, raw16537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16537step0 = (fun i j => raw16537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16537step0 raw16537; decide +kernel
      have hl : raw16537step0Labels = raw16537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16537 raw16537Labels permutation346 hz
    mixedMoment B raw16537step0 raw16537step0Labels = mixedMoment B raw16537step1 raw16537step1Labels := by
      have ha : raw16537step1 = (fun i j => raw16537step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16537step1 raw16537step0; decide +kernel
      have hl : raw16537step1Labels = raw16537step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16537step0 raw16537step0Labels permutation151 permutation2
    mixedMoment B raw16537step1 raw16537step1Labels = mixedMoment B raw16537step2 raw16537step2Labels := by
      have ha : raw16537step2 = -raw16537step1 := by apply Matrix.ext; change ∀ i j, raw16537step2 i j = -(raw16537step1 i j); unfold raw16537step2 raw16537step1; decide +kernel
      have hl : raw16537step2Labels = raw16537step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2866 node2866Labels := by rfl

def raw16538 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw16538Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16538step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw16538step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16538step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw16538step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16538step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw16538step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical16538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16538 raw16538Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw16538 raw16538Labels = mixedMoment B raw16538step0 raw16538step0Labels := by
      have hz : ∀ j, raw16538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16538step0 = (fun i j => raw16538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16538step0 raw16538; decide +kernel
      have hl : raw16538step0Labels = raw16538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16538 raw16538Labels permutation346 hz
    mixedMoment B raw16538step0 raw16538step0Labels = mixedMoment B raw16538step1 raw16538step1Labels := by
      have hz : ∀ j, raw16538step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw16538step1 = (fun i j => raw16538step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw16538step1 raw16538step0; decide +kernel
      have hl : raw16538step1Labels = raw16538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16538step0 raw16538step0Labels permutation32 hz
    mixedMoment B raw16538step1 raw16538step1Labels = mixedMoment B raw16538step2 raw16538step2Labels := by
      have ha : raw16538step2 = (fun i j => raw16538step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16538step2 raw16538step1; decide +kernel
      have hl : raw16538step2Labels = raw16538step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16538step1 raw16538step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw16539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16539 raw16539Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw16539 raw16539Labels = mixedMoment B raw16539step0 raw16539step0Labels := by
      have hz : ∀ j, raw16539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16539step0 = (fun i j => raw16539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16539step0 raw16539; decide +kernel
      have hl : raw16539step0Labels = raw16539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16539 raw16539Labels permutation346 hz
    mixedMoment B raw16539step0 raw16539step0Labels = mixedMoment B raw16539step1 raw16539step1Labels := by
      have ha : raw16539step1 = (fun i j => raw16539step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16539step1 raw16539step0; decide +kernel
      have hl : raw16539step1Labels = raw16539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16539step0 raw16539step0Labels permutation56 permutation2
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw16540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16540 raw16540Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw16540 raw16540Labels = mixedMoment B raw16540step0 raw16540step0Labels := by
      have ha : raw16540step0 = (fun i j => raw16540 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16540step0 raw16540; decide +kernel
      have hl : raw16540step0Labels = raw16540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16540 raw16540Labels permutation271 permutation2
    _ = mixedMoment B node3720 node3720Labels := by rfl

def raw16541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16541 raw16541Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw16541 raw16541Labels = mixedMoment B raw16541step0 raw16541step0Labels := by
      have hz : ∀ j, raw16541 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16541step0 = (fun i j => raw16541 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16541step0 raw16541; decide +kernel
      have hl : raw16541step0Labels = raw16541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16541 raw16541Labels permutation346 hz
    mixedMoment B raw16541step0 raw16541step0Labels = mixedMoment B raw16541step1 raw16541step1Labels := by
      have ha : raw16541step1 = (fun i j => raw16541step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16541step1 raw16541step0; decide +kernel
      have hl : raw16541step1Labels = raw16541step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16541step0 raw16541step0Labels permutation56 permutation2
    _ = mixedMoment B node3733 node3733Labels := by rfl

def raw16542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16542 raw16542Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw16542 raw16542Labels = mixedMoment B raw16542step0 raw16542step0Labels := by
      have hz : ∀ j, raw16542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16542step0 = (fun i j => raw16542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16542step0 raw16542; decide +kernel
      have hl : raw16542step0Labels = raw16542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16542 raw16542Labels permutation346 hz
    mixedMoment B raw16542step0 raw16542step0Labels = mixedMoment B raw16542step1 raw16542step1Labels := by
      have ha : raw16542step1 = (fun i j => raw16542step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16542step1 raw16542step0; decide +kernel
      have hl : raw16542step1Labels = raw16542step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16542step0 raw16542step0Labels permutation126 permutation2
    mixedMoment B raw16542step1 raw16542step1Labels = mixedMoment B raw16542step2 raw16542step2Labels := by
      have ha : raw16542step2 = -raw16542step1 := by apply Matrix.ext; change ∀ i j, raw16542step2 i j = -(raw16542step1 i j); unfold raw16542step2 raw16542step1; decide +kernel
      have hl : raw16542step2Labels = raw16542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw16543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16543 raw16543Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw16543 raw16543Labels = mixedMoment B raw16543step0 raw16543step0Labels := by
      have hz : ∀ j, raw16543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16543step0 = (fun i j => raw16543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16543step0 raw16543; decide +kernel
      have hl : raw16543step0Labels = raw16543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16543 raw16543Labels permutation346 hz
    mixedMoment B raw16543step0 raw16543step0Labels = mixedMoment B raw16543step1 raw16543step1Labels := by
      have ha : raw16543step1 = (fun i j => raw16543step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16543step1 raw16543step0; decide +kernel
      have hl : raw16543step1Labels = raw16543step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16543step0 raw16543step0Labels permutation150 permutation2
    mixedMoment B raw16543step1 raw16543step1Labels = mixedMoment B raw16543step2 raw16543step2Labels := by
      have ha : raw16543step2 = -raw16543step1 := by apply Matrix.ext; change ∀ i j, raw16543step2 i j = -(raw16543step1 i j); unfold raw16543step2 raw16543step1; decide +kernel
      have hl : raw16543step2Labels = raw16543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw16544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16544 raw16544Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw16544 raw16544Labels = mixedMoment B raw16544step0 raw16544step0Labels := by
      have ha : raw16544step0 = (fun i j => raw16544 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16544step0 raw16544; decide +kernel
      have hl : raw16544step0Labels = raw16544Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16544 raw16544Labels permutation682 permutation2
    mixedMoment B raw16544step0 raw16544step0Labels = mixedMoment B raw16544step1 raw16544step1Labels := by
      have ha : raw16544step1 = -raw16544step0 := by apply Matrix.ext; change ∀ i j, raw16544step1 i j = -(raw16544step0 i j); unfold raw16544step1 raw16544step0; decide +kernel
      have hl : raw16544step1Labels = raw16544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3946 node3946Labels := by rfl

def raw16545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16545 raw16545Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw16545 raw16545Labels = mixedMoment B raw16545step0 raw16545step0Labels := by
      have ha : raw16545step0 = (fun i j => raw16545 (permutation528 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16545step0 raw16545; decide +kernel
      have hl : raw16545step0Labels = raw16545Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16545 raw16545Labels permutation528 permutation4
    mixedMoment B raw16545step0 raw16545step0Labels = mixedMoment B raw16545step1 raw16545step1Labels := by
      have ha : raw16545step1 = -raw16545step0 := by apply Matrix.ext; change ∀ i j, raw16545step1 i j = -(raw16545step0 i j); unfold raw16545step1 raw16545step0; decide +kernel
      have hl : raw16545step1Labels = raw16545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3730 node3730Labels := by rfl

def raw16546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16546 raw16546Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw16546 raw16546Labels = mixedMoment B raw16546step0 raw16546step0Labels := by
      have ha : raw16546step0 = (fun i j => raw16546 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16546step0 raw16546; decide +kernel
      have hl : raw16546step0Labels = raw16546Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16546 raw16546Labels permutation159 permutation2
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw16547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16547 raw16547Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw16547 raw16547Labels = mixedMoment B raw16547step0 raw16547step0Labels := by
      have ha : raw16547step0 = (fun i j => raw16547 (permutation684 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16547step0 raw16547; decide +kernel
      have hl : raw16547step0Labels = raw16547Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16547 raw16547Labels permutation684 permutation2
    mixedMoment B raw16547step0 raw16547step0Labels = mixedMoment B raw16547step1 raw16547step1Labels := by
      have ha : raw16547step1 = -raw16547step0 := by apply Matrix.ext; change ∀ i j, raw16547step1 i j = -(raw16547step0 i j); unfold raw16547step1 raw16547step0; decide +kernel
      have hl : raw16547step1Labels = raw16547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw16548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16548 raw16548Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw16548 raw16548Labels = mixedMoment B raw16548step0 raw16548step0Labels := by
      have ha : raw16548step0 = (fun i j => raw16548 (permutation319 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16548step0 raw16548; decide +kernel
      have hl : raw16548step0Labels = raw16548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16548 raw16548Labels permutation319 permutation4
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw16549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16549 raw16549Labels = mixedMoment B node3948 node3948Labels := by
  calc
    mixedMoment B raw16549 raw16549Labels = mixedMoment B raw16549step0 raw16549step0Labels := by
      have ha : raw16549step0 = (fun i j => raw16549 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16549step0 raw16549; decide +kernel
      have hl : raw16549step0Labels = raw16549Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16549 raw16549Labels permutation688 permutation2
    mixedMoment B raw16549step0 raw16549step0Labels = mixedMoment B raw16549step1 raw16549step1Labels := by
      have ha : raw16549step1 = -raw16549step0 := by apply Matrix.ext; change ∀ i j, raw16549step1 i j = -(raw16549step0 i j); unfold raw16549step1 raw16549step0; decide +kernel
      have hl : raw16549step1Labels = raw16549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3948 node3948Labels := by rfl

def raw16550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16550 raw16550Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw16550 raw16550Labels = mixedMoment B raw16550step0 raw16550step0Labels := by
      have ha : raw16550step0 = (fun i j => raw16550 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16550step0 raw16550; decide +kernel
      have hl : raw16550step0Labels = raw16550Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16550 raw16550Labels permutation589 permutation2
    mixedMoment B raw16550step0 raw16550step0Labels = mixedMoment B raw16550step1 raw16550step1Labels := by
      have ha : raw16550step1 = -raw16550step0 := by apply Matrix.ext; change ∀ i j, raw16550step1 i j = -(raw16550step0 i j); unfold raw16550step1 raw16550step0; decide +kernel
      have hl : raw16550step1Labels = raw16550step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3691 node3691Labels := by rfl

def raw16551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16551 raw16551Labels = mixedMoment B node2863 node2863Labels := by
  calc
    mixedMoment B raw16551 raw16551Labels = mixedMoment B raw16551step0 raw16551step0Labels := by
      have ha : raw16551step0 = (fun i j => raw16551 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16551step0 raw16551; decide +kernel
      have hl : raw16551step0Labels = raw16551Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16551 raw16551Labels permutation688 permutation2
    mixedMoment B raw16551step0 raw16551step0Labels = mixedMoment B raw16551step1 raw16551step1Labels := by
      have ha : raw16551step1 = -raw16551step0 := by apply Matrix.ext; change ∀ i j, raw16551step1 i j = -(raw16551step0 i j); unfold raw16551step1 raw16551step0; decide +kernel
      have hl : raw16551step1Labels = raw16551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2863 node2863Labels := by rfl

def raw16552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16552 raw16552Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw16552 raw16552Labels = mixedMoment B raw16552step0 raw16552step0Labels := by
      have hz : ∀ j, raw16552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16552step0 = (fun i j => raw16552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16552step0 raw16552; decide +kernel
      have hl : raw16552step0Labels = raw16552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16552 raw16552Labels permutation346 hz
    mixedMoment B raw16552step0 raw16552step0Labels = mixedMoment B raw16552step1 raw16552step1Labels := by
      have ha : raw16552step1 = (fun i j => raw16552step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16552step1 raw16552step0; decide +kernel
      have hl : raw16552step1Labels = raw16552step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16552step0 raw16552step0Labels permutation108 permutation4
    mixedMoment B raw16552step1 raw16552step1Labels = mixedMoment B raw16552step2 raw16552step2Labels := by
      have ha : raw16552step2 = -raw16552step1 := by apply Matrix.ext; change ∀ i j, raw16552step2 i j = -(raw16552step1 i j); unfold raw16552step2 raw16552step1; decide +kernel
      have hl : raw16552step2Labels = raw16552step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3733 node3733Labels := by rfl

def raw16553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16553 raw16553Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw16553 raw16553Labels = mixedMoment B raw16553step0 raw16553step0Labels := by
      have hz : ∀ j, raw16553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16553step0 = (fun i j => raw16553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16553step0 raw16553; decide +kernel
      have hl : raw16553step0Labels = raw16553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16553 raw16553Labels permutation346 hz
    mixedMoment B raw16553step0 raw16553step0Labels = mixedMoment B raw16553step1 raw16553step1Labels := by
      have ha : raw16553step1 = (fun i j => raw16553step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16553step1 raw16553step0; decide +kernel
      have hl : raw16553step1Labels = raw16553step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16553step0 raw16553step0Labels permutation91 permutation4
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw16554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16554 raw16554Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw16554 raw16554Labels = mixedMoment B raw16554step0 raw16554step0Labels := by
      have hz : ∀ j, raw16554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16554step0 = (fun i j => raw16554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16554step0 raw16554; decide +kernel
      have hl : raw16554step0Labels = raw16554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16554 raw16554Labels permutation346 hz
    mixedMoment B raw16554step0 raw16554step0Labels = mixedMoment B raw16554step1 raw16554step1Labels := by
      have ha : raw16554step1 = (fun i j => raw16554step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16554step1 raw16554step0; decide +kernel
      have hl : raw16554step1Labels = raw16554step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16554step0 raw16554step0Labels permutation127 permutation2
    mixedMoment B raw16554step1 raw16554step1Labels = mixedMoment B raw16554step2 raw16554step2Labels := by
      have ha : raw16554step2 = -raw16554step1 := by apply Matrix.ext; change ∀ i j, raw16554step2 i j = -(raw16554step1 i j); unfold raw16554step2 raw16554step1; decide +kernel
      have hl : raw16554step2Labels = raw16554step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw16555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16555 raw16555Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw16555 raw16555Labels = mixedMoment B raw16555step0 raw16555step0Labels := by
      have hz : ∀ j, raw16555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16555step0 = (fun i j => raw16555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16555step0 raw16555; decide +kernel
      have hl : raw16555step0Labels = raw16555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16555 raw16555Labels permutation346 hz
    mixedMoment B raw16555step0 raw16555step0Labels = mixedMoment B raw16555step1 raw16555step1Labels := by
      have ha : raw16555step1 = (fun i j => raw16555step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16555step1 raw16555step0; decide +kernel
      have hl : raw16555step1Labels = raw16555step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16555step0 raw16555step0Labels permutation127 permutation2
    mixedMoment B raw16555step1 raw16555step1Labels = mixedMoment B raw16555step2 raw16555step2Labels := by
      have ha : raw16555step2 = -raw16555step1 := by apply Matrix.ext; change ∀ i j, raw16555step2 i j = -(raw16555step1 i j); unfold raw16555step2 raw16555step1; decide +kernel
      have hl : raw16555step2Labels = raw16555step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw16556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16556 raw16556Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw16556 raw16556Labels = mixedMoment B raw16556step0 raw16556step0Labels := by
      have hz : ∀ j, raw16556 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16556step0 = (fun i j => raw16556 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16556step0 raw16556; decide +kernel
      have hl : raw16556step0Labels = raw16556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16556 raw16556Labels permutation346 hz
    mixedMoment B raw16556step0 raw16556step0Labels = mixedMoment B raw16556step1 raw16556step1Labels := by
      have ha : raw16556step1 = (fun i j => raw16556step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16556step1 raw16556step0; decide +kernel
      have hl : raw16556step1Labels = raw16556step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16556step0 raw16556step0Labels permutation109 permutation4
    mixedMoment B raw16556step1 raw16556step1Labels = mixedMoment B raw16556step2 raw16556step2Labels := by
      have ha : raw16556step2 = -raw16556step1 := by apply Matrix.ext; change ∀ i j, raw16556step2 i j = -(raw16556step1 i j); unfold raw16556step2 raw16556step1; decide +kernel
      have hl : raw16556step2Labels = raw16556step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw16557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16557step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16557 raw16557Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw16557 raw16557Labels = mixedMoment B raw16557step0 raw16557step0Labels := by
      have hz : ∀ j, raw16557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16557step0 = (fun i j => raw16557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16557step0 raw16557; decide +kernel
      have hl : raw16557step0Labels = raw16557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16557 raw16557Labels permutation346 hz
    mixedMoment B raw16557step0 raw16557step0Labels = mixedMoment B raw16557step1 raw16557step1Labels := by
      have ha : raw16557step1 = (fun i j => raw16557step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16557step1 raw16557step0; decide +kernel
      have hl : raw16557step1Labels = raw16557step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16557step0 raw16557step0Labels permutation109 permutation4
    mixedMoment B raw16557step1 raw16557step1Labels = mixedMoment B raw16557step2 raw16557step2Labels := by
      have ha : raw16557step2 = -raw16557step1 := by apply Matrix.ext; change ∀ i j, raw16557step2 i j = -(raw16557step1 i j); unfold raw16557step2 raw16557step1; decide +kernel
      have hl : raw16557step2Labels = raw16557step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw16558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16558 raw16558Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw16558 raw16558Labels = mixedMoment B raw16558step0 raw16558step0Labels := by
      have hz : ∀ j, raw16558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16558step0 = (fun i j => raw16558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16558step0 raw16558; decide +kernel
      have hl : raw16558step0Labels = raw16558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16558 raw16558Labels permutation346 hz
    mixedMoment B raw16558step0 raw16558step0Labels = mixedMoment B raw16558step1 raw16558step1Labels := by
      have ha : raw16558step1 = (fun i j => raw16558step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16558step1 raw16558step0; decide +kernel
      have hl : raw16558step1Labels = raw16558step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16558step0 raw16558step0Labels permutation151 permutation2
    mixedMoment B raw16558step1 raw16558step1Labels = mixedMoment B raw16558step2 raw16558step2Labels := by
      have ha : raw16558step2 = -raw16558step1 := by apply Matrix.ext; change ∀ i j, raw16558step2 i j = -(raw16558step1 i j); unfold raw16558step2 raw16558step1; decide +kernel
      have hl : raw16558step2Labels = raw16558step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3040 node3040Labels := by rfl

def raw16559 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16559step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16559step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16559 raw16559Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw16559 raw16559Labels = mixedMoment B raw16559step0 raw16559step0Labels := by
      have hz : ∀ j, raw16559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16559step0 = (fun i j => raw16559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16559step0 raw16559; decide +kernel
      have hl : raw16559step0Labels = raw16559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16559 raw16559Labels permutation346 hz
    mixedMoment B raw16559step0 raw16559step0Labels = mixedMoment B raw16559step1 raw16559step1Labels := by
      have ha : raw16559step1 = (fun i j => raw16559step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16559step1 raw16559step0; decide +kernel
      have hl : raw16559step1Labels = raw16559step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16559step0 raw16559step0Labels permutation123 permutation3
    mixedMoment B raw16559step1 raw16559step1Labels = mixedMoment B raw16559step2 raw16559step2Labels := by
      have ha : raw16559step2 = raw16559step1 := by apply Matrix.ext; unfold raw16559step2 raw16559step1; decide +kernel
      have hl : raw16559step1Labels = labelEmbedding6 ∘ raw16559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16559step1 raw16559step1Labels raw16559step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw16560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16560 raw16560Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw16560 raw16560Labels = mixedMoment B raw16560step0 raw16560step0Labels := by
      have hz : ∀ j, raw16560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16560step0 = (fun i j => raw16560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16560step0 raw16560; decide +kernel
      have hl : raw16560step0Labels = raw16560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16560 raw16560Labels permutation346 hz
    mixedMoment B raw16560step0 raw16560step0Labels = mixedMoment B raw16560step1 raw16560step1Labels := by
      have ha : raw16560step1 = (fun i j => raw16560step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16560step1 raw16560step0; decide +kernel
      have hl : raw16560step1Labels = raw16560step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16560step0 raw16560step0Labels permutation150 permutation2
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw16561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw16561step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw16561step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16561step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw16561step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16561 raw16561Labels = mixedMoment B node5096 node5096Labels := by
  calc
    mixedMoment B raw16561 raw16561Labels = mixedMoment B raw16561step0 raw16561step0Labels := by
      have hz : ∀ j, raw16561 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16561step0 = (fun i j => raw16561 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16561step0 raw16561; decide +kernel
      have hl : raw16561step0Labels = raw16561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16561 raw16561Labels permutation346 hz
    mixedMoment B raw16561step0 raw16561step0Labels = mixedMoment B raw16561step1 raw16561step1Labels := by
      have ha : raw16561step1 = (fun i j => raw16561step0 (permutation66 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16561step1 raw16561step0; decide +kernel
      have hl : raw16561step1Labels = raw16561step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16561step0 raw16561step0Labels permutation66 permutation3
    mixedMoment B raw16561step1 raw16561step1Labels = mixedMoment B raw16561step2 raw16561step2Labels := by
      have ha : raw16561step2 = -raw16561step1 := by apply Matrix.ext; change ∀ i j, raw16561step2 i j = -(raw16561step1 i j); unfold raw16561step2 raw16561step1; decide +kernel
      have hl : raw16561step2Labels = raw16561step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16561step2 raw16561step2Labels = mixedMoment B raw16561step3 raw16561step3Labels := by
      have ha : raw16561step3 = raw16561step2 := by apply Matrix.ext; unfold raw16561step3 raw16561step2; decide +kernel
      have hl : raw16561step2Labels = labelEmbedding6 ∘ raw16561step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16561step2 raw16561step2Labels raw16561step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5096 node5096Labels := by rfl

def raw16562 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw16562step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw16562step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16562step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw16562step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16562 raw16562Labels = mixedMoment B node5084 node5084Labels := by
  calc
    mixedMoment B raw16562 raw16562Labels = mixedMoment B raw16562step0 raw16562step0Labels := by
      have hz : ∀ j, raw16562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16562step0 = (fun i j => raw16562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16562step0 raw16562; decide +kernel
      have hl : raw16562step0Labels = raw16562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16562 raw16562Labels permutation346 hz
    mixedMoment B raw16562step0 raw16562step0Labels = mixedMoment B raw16562step1 raw16562step1Labels := by
      have ha : raw16562step1 = (fun i j => raw16562step0 (permutation63 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16562step1 raw16562step0; decide +kernel
      have hl : raw16562step1Labels = raw16562step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16562step0 raw16562step0Labels permutation63 permutation3
    mixedMoment B raw16562step1 raw16562step1Labels = mixedMoment B raw16562step2 raw16562step2Labels := by
      have ha : raw16562step2 = -raw16562step1 := by apply Matrix.ext; change ∀ i j, raw16562step2 i j = -(raw16562step1 i j); unfold raw16562step2 raw16562step1; decide +kernel
      have hl : raw16562step2Labels = raw16562step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16562step2 raw16562step2Labels = mixedMoment B raw16562step3 raw16562step3Labels := by
      have ha : raw16562step3 = raw16562step2 := by apply Matrix.ext; unfold raw16562step3 raw16562step2; decide +kernel
      have hl : raw16562step2Labels = labelEmbedding6 ∘ raw16562step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16562step2 raw16562step2Labels raw16562step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5084 node5084Labels := by rfl

def raw16563 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw16563step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16563step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16563step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16563step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16563 raw16563Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw16563 raw16563Labels = mixedMoment B raw16563step0 raw16563step0Labels := by
      have hz : ∀ j, raw16563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16563step0 = (fun i j => raw16563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16563step0 raw16563; decide +kernel
      have hl : raw16563step0Labels = raw16563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16563 raw16563Labels permutation346 hz
    mixedMoment B raw16563step0 raw16563step0Labels = mixedMoment B raw16563step1 raw16563step1Labels := by
      have ha : raw16563step1 = (fun i j => raw16563step0 (permutation63 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16563step1 raw16563step0; decide +kernel
      have hl : raw16563step1Labels = raw16563step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16563step0 raw16563step0Labels permutation63 permutation3
    mixedMoment B raw16563step1 raw16563step1Labels = mixedMoment B raw16563step2 raw16563step2Labels := by
      have ha : raw16563step2 = -raw16563step1 := by apply Matrix.ext; change ∀ i j, raw16563step2 i j = -(raw16563step1 i j); unfold raw16563step2 raw16563step1; decide +kernel
      have hl : raw16563step2Labels = raw16563step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16563step2 raw16563step2Labels = mixedMoment B raw16563step3 raw16563step3Labels := by
      have ha : raw16563step3 = raw16563step2 := by apply Matrix.ext; unfold raw16563step3 raw16563step2; decide +kernel
      have hl : raw16563step2Labels = labelEmbedding6 ∘ raw16563step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16563step2 raw16563step2Labels raw16563step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw16564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16564step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16564step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16564step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16564step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16564 raw16564Labels = mixedMoment B node5200 node5200Labels := by
  calc
    mixedMoment B raw16564 raw16564Labels = mixedMoment B raw16564step0 raw16564step0Labels := by
      have hz : ∀ j, raw16564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16564step0 = (fun i j => raw16564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16564step0 raw16564; decide +kernel
      have hl : raw16564step0Labels = raw16564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16564 raw16564Labels permutation346 hz
    mixedMoment B raw16564step0 raw16564step0Labels = mixedMoment B raw16564step1 raw16564step1Labels := by
      have ha : raw16564step1 = (fun i j => raw16564step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16564step1 raw16564step0; decide +kernel
      have hl : raw16564step1Labels = raw16564step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16564step0 raw16564step0Labels permutation45 permutation4
    mixedMoment B raw16564step1 raw16564step1Labels = mixedMoment B raw16564step2 raw16564step2Labels := by
      have ha : raw16564step2 = -raw16564step1 := by apply Matrix.ext; change ∀ i j, raw16564step2 i j = -(raw16564step1 i j); unfold raw16564step2 raw16564step1; decide +kernel
      have hl : raw16564step2Labels = raw16564step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16564step2 raw16564step2Labels = mixedMoment B raw16564step3 raw16564step3Labels := by
      have ha : raw16564step3 = raw16564step2 := by apply Matrix.ext; unfold raw16564step3 raw16564step2; decide +kernel
      have hl : raw16564step2Labels = labelEmbedding7 ∘ raw16564step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16564step2 raw16564step2Labels raw16564step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5200 node5200Labels := by rfl

def raw16565 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw16565step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw16565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16565 raw16565Labels = mixedMoment B node5180 node5180Labels := by
  calc
    mixedMoment B raw16565 raw16565Labels = mixedMoment B raw16565step0 raw16565step0Labels := by
      have hz : ∀ j, raw16565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16565step0 = (fun i j => raw16565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16565step0 raw16565; decide +kernel
      have hl : raw16565step0Labels = raw16565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16565 raw16565Labels permutation346 hz
    mixedMoment B raw16565step0 raw16565step0Labels = mixedMoment B raw16565step1 raw16565step1Labels := by
      have ha : raw16565step1 = (fun i j => raw16565step0 (permutation122 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16565step1 raw16565step0; decide +kernel
      have hl : raw16565step1Labels = raw16565step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16565step0 raw16565step0Labels permutation122 permutation3
    mixedMoment B raw16565step1 raw16565step1Labels = mixedMoment B raw16565step2 raw16565step2Labels := by
      have ha : raw16565step2 = raw16565step1 := by apply Matrix.ext; unfold raw16565step2 raw16565step1; decide +kernel
      have hl : raw16565step1Labels = labelEmbedding6 ∘ raw16565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16565step1 raw16565step1Labels raw16565step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5180 node5180Labels := by rfl

def raw16566 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16566 raw16566Labels = mixedMoment B node5361 node5361Labels := by
  calc
    mixedMoment B raw16566 raw16566Labels = mixedMoment B raw16566step0 raw16566step0Labels := by
      have hz : ∀ j, raw16566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16566step0 = (fun i j => raw16566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16566step0 raw16566; decide +kernel
      have hl : raw16566step0Labels = raw16566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16566 raw16566Labels permutation346 hz
    mixedMoment B raw16566step0 raw16566step0Labels = mixedMoment B raw16566step1 raw16566step1Labels := by
      have ha : raw16566step1 = (fun i j => raw16566step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16566step1 raw16566step0; decide +kernel
      have hl : raw16566step1Labels = raw16566step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16566step0 raw16566step0Labels permutation147 permutation2
    _ = mixedMoment B node5361 node5361Labels := by rfl

def raw16567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16567step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16567step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16567step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16567step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16567 raw16567Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw16567 raw16567Labels = mixedMoment B raw16567step0 raw16567step0Labels := by
      have hz : ∀ j, raw16567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16567step0 = (fun i j => raw16567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16567step0 raw16567; decide +kernel
      have hl : raw16567step0Labels = raw16567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16567 raw16567Labels permutation346 hz
    mixedMoment B raw16567step0 raw16567step0Labels = mixedMoment B raw16567step1 raw16567step1Labels := by
      have ha : raw16567step1 = (fun i j => raw16567step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16567step1 raw16567step0; decide +kernel
      have hl : raw16567step1Labels = raw16567step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16567step0 raw16567step0Labels permutation44 permutation4
    mixedMoment B raw16567step1 raw16567step1Labels = mixedMoment B raw16567step2 raw16567step2Labels := by
      have ha : raw16567step2 = -raw16567step1 := by apply Matrix.ext; change ∀ i j, raw16567step2 i j = -(raw16567step1 i j); unfold raw16567step2 raw16567step1; decide +kernel
      have hl : raw16567step2Labels = raw16567step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16567step2 raw16567step2Labels = mixedMoment B raw16567step3 raw16567step3Labels := by
      have ha : raw16567step3 = raw16567step2 := by apply Matrix.ext; unfold raw16567step3 raw16567step2; decide +kernel
      have hl : raw16567step2Labels = labelEmbedding7 ∘ raw16567step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16567step2 raw16567step2Labels raw16567step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw16568 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16568step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16568 raw16568Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw16568 raw16568Labels = mixedMoment B raw16568step0 raw16568step0Labels := by
      have hz : ∀ j, raw16568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16568step0 = (fun i j => raw16568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16568step0 raw16568; decide +kernel
      have hl : raw16568step0Labels = raw16568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16568 raw16568Labels permutation346 hz
    mixedMoment B raw16568step0 raw16568step0Labels = mixedMoment B raw16568step1 raw16568step1Labels := by
      have ha : raw16568step1 = (fun i j => raw16568step0 (permutation109 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16568step1 raw16568step0; decide +kernel
      have hl : raw16568step1Labels = raw16568step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16568step0 raw16568step0Labels permutation109 permutation3
    mixedMoment B raw16568step1 raw16568step1Labels = mixedMoment B raw16568step2 raw16568step2Labels := by
      have ha : raw16568step2 = raw16568step1 := by apply Matrix.ext; unfold raw16568step2 raw16568step1; decide +kernel
      have hl : raw16568step1Labels = labelEmbedding6 ∘ raw16568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16568step1 raw16568step1Labels raw16568step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw16569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16569step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16569 raw16569Labels = mixedMoment B node4004 node4004Labels := by
  calc
    mixedMoment B raw16569 raw16569Labels = mixedMoment B raw16569step0 raw16569step0Labels := by
      have hz : ∀ j, raw16569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16569step0 = (fun i j => raw16569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16569step0 raw16569; decide +kernel
      have hl : raw16569step0Labels = raw16569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16569 raw16569Labels permutation434 hz
    mixedMoment B raw16569step0 raw16569step0Labels = mixedMoment B raw16569step1 raw16569step1Labels := by
      have hz : ∀ j, raw16569step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16569step1 = (fun i j => raw16569step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16569step1 raw16569step0; decide +kernel
      have hl : raw16569step1Labels = raw16569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16569step0 raw16569step0Labels permutation80 hz
    mixedMoment B raw16569step1 raw16569step1Labels = mixedMoment B raw16569step2 raw16569step2Labels := by
      have ha : raw16569step2 = (fun i j => raw16569step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16569step2 raw16569step1; decide +kernel
      have hl : raw16569step2Labels = raw16569step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16569step1 raw16569step1Labels permutation24 permutation3
    _ = mixedMoment B node4004 node4004Labels := by rfl

def raw16570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16570step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16570 raw16570Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw16570 raw16570Labels = mixedMoment B raw16570step0 raw16570step0Labels := by
      have hz : ∀ j, raw16570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16570step0 = (fun i j => raw16570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16570step0 raw16570; decide +kernel
      have hl : raw16570step0Labels = raw16570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16570 raw16570Labels permutation346 hz
    mixedMoment B raw16570step0 raw16570step0Labels = mixedMoment B raw16570step1 raw16570step1Labels := by
      have ha : raw16570step1 = (fun i j => raw16570step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16570step1 raw16570step0; decide +kernel
      have hl : raw16570step1Labels = raw16570step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16570step0 raw16570step0Labels permutation123 permutation3
    _ = mixedMoment B node2633 node2633Labels := by rfl

def raw16571 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16571 raw16571Labels = mixedMoment B node3939 node3939Labels := by
  calc
    mixedMoment B raw16571 raw16571Labels = mixedMoment B raw16571step0 raw16571step0Labels := by
      have hz : ∀ j, raw16571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16571step0 = (fun i j => raw16571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16571step0 raw16571; decide +kernel
      have hl : raw16571step0Labels = raw16571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16571 raw16571Labels permutation346 hz
    mixedMoment B raw16571step0 raw16571step0Labels = mixedMoment B raw16571step1 raw16571step1Labels := by
      have ha : raw16571step1 = (fun i j => raw16571step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16571step1 raw16571step0; decide +kernel
      have hl : raw16571step1Labels = raw16571step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16571step0 raw16571step0Labels permutation123 permutation3
    _ = mixedMoment B node3939 node3939Labels := by rfl

def raw16572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw16572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw16572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16572 raw16572Labels = mixedMoment B node2506 node2506Labels := by
  calc
    mixedMoment B raw16572 raw16572Labels = mixedMoment B raw16572step0 raw16572step0Labels := by
      have hz : ∀ j, raw16572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16572step0 = (fun i j => raw16572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16572step0 raw16572; decide +kernel
      have hl : raw16572step0Labels = raw16572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16572 raw16572Labels permutation346 hz
    mixedMoment B raw16572step0 raw16572step0Labels = mixedMoment B raw16572step1 raw16572step1Labels := by
      have ha : raw16572step1 = (fun i j => raw16572step0 (permutation66 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16572step1 raw16572step0; decide +kernel
      have hl : raw16572step1Labels = raw16572step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16572step0 raw16572step0Labels permutation66 permutation3
    mixedMoment B raw16572step1 raw16572step1Labels = mixedMoment B raw16572step2 raw16572step2Labels := by
      have ha : raw16572step2 = -raw16572step1 := by apply Matrix.ext; change ∀ i j, raw16572step2 i j = -(raw16572step1 i j); unfold raw16572step2 raw16572step1; decide +kernel
      have hl : raw16572step2Labels = raw16572step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2506 node2506Labels := by rfl

def raw16573 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16573step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16573step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16573 raw16573Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw16573 raw16573Labels = mixedMoment B raw16573step0 raw16573step0Labels := by
      have hz : ∀ j, raw16573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16573step0 = (fun i j => raw16573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16573step0 raw16573; decide +kernel
      have hl : raw16573step0Labels = raw16573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16573 raw16573Labels permutation434 hz
    mixedMoment B raw16573step0 raw16573step0Labels = mixedMoment B raw16573step1 raw16573step1Labels := by
      have hz : ∀ j, raw16573step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16573step1 = (fun i j => raw16573step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16573step1 raw16573step0; decide +kernel
      have hl : raw16573step1Labels = raw16573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16573step0 raw16573step0Labels permutation80 hz
    mixedMoment B raw16573step1 raw16573step1Labels = mixedMoment B raw16573step2 raw16573step2Labels := by
      have ha : raw16573step2 = (fun i j => raw16573step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16573step2 raw16573step1; decide +kernel
      have hl : raw16573step2Labels = raw16573step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16573step1 raw16573step1Labels permutation15 permutation3
    mixedMoment B raw16573step2 raw16573step2Labels = mixedMoment B raw16573step3 raw16573step3Labels := by
      have ha : raw16573step3 = -raw16573step2 := by apply Matrix.ext; change ∀ i j, raw16573step3 i j = -(raw16573step2 i j); unfold raw16573step3 raw16573step2; decide +kernel
      have hl : raw16573step3Labels = raw16573step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw16574 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16574step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw16574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw16574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16574 raw16574Labels = mixedMoment B node2492 node2492Labels := by
  calc
    mixedMoment B raw16574 raw16574Labels = mixedMoment B raw16574step0 raw16574step0Labels := by
      have hz : ∀ j, raw16574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16574step0 = (fun i j => raw16574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16574step0 raw16574; decide +kernel
      have hl : raw16574step0Labels = raw16574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16574 raw16574Labels permutation346 hz
    mixedMoment B raw16574step0 raw16574step0Labels = mixedMoment B raw16574step1 raw16574step1Labels := by
      have ha : raw16574step1 = (fun i j => raw16574step0 (permutation63 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16574step1 raw16574step0; decide +kernel
      have hl : raw16574step1Labels = raw16574step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16574step0 raw16574step0Labels permutation63 permutation3
    mixedMoment B raw16574step1 raw16574step1Labels = mixedMoment B raw16574step2 raw16574step2Labels := by
      have ha : raw16574step2 = -raw16574step1 := by apply Matrix.ext; change ∀ i j, raw16574step2 i j = -(raw16574step1 i j); unfold raw16574step2 raw16574step1; decide +kernel
      have hl : raw16574step2Labels = raw16574step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2492 node2492Labels := by rfl

def raw16575 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw16575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16575 raw16575Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw16575 raw16575Labels = mixedMoment B raw16575step0 raw16575step0Labels := by
      have hz : ∀ j, raw16575 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16575step0 = (fun i j => raw16575 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16575step0 raw16575; decide +kernel
      have hl : raw16575step0Labels = raw16575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16575 raw16575Labels permutation346 hz
    mixedMoment B raw16575step0 raw16575step0Labels = mixedMoment B raw16575step1 raw16575step1Labels := by
      have ha : raw16575step1 = (fun i j => raw16575step0 (permutation63 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16575step1 raw16575step0; decide +kernel
      have hl : raw16575step1Labels = raw16575step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16575step0 raw16575step0Labels permutation63 permutation3
    mixedMoment B raw16575step1 raw16575step1Labels = mixedMoment B raw16575step2 raw16575step2Labels := by
      have ha : raw16575step2 = -raw16575step1 := by apply Matrix.ext; change ∀ i j, raw16575step2 i j = -(raw16575step1 i j); unfold raw16575step2 raw16575step1; decide +kernel
      have hl : raw16575step2Labels = raw16575step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2499 node2499Labels := by rfl

def raw16576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16576 raw16576Labels = mixedMoment B node3575 node3575Labels := by
  calc
    mixedMoment B raw16576 raw16576Labels = mixedMoment B raw16576step0 raw16576step0Labels := by
      have hz : ∀ j, raw16576 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16576step0 = (fun i j => raw16576 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16576step0 raw16576; decide +kernel
      have hl : raw16576step0Labels = raw16576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16576 raw16576Labels permutation346 hz
    mixedMoment B raw16576step0 raw16576step0Labels = mixedMoment B raw16576step1 raw16576step1Labels := by
      have ha : raw16576step1 = (fun i j => raw16576step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16576step1 raw16576step0; decide +kernel
      have hl : raw16576step1Labels = raw16576step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16576step0 raw16576step0Labels permutation32 permutation6
    _ = mixedMoment B node3575 node3575Labels := by rfl

def raw16577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw16577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16577 raw16577Labels = mixedMoment B node2608 node2608Labels := by
  calc
    mixedMoment B raw16577 raw16577Labels = mixedMoment B raw16577step0 raw16577step0Labels := by
      have hz : ∀ j, raw16577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16577step0 = (fun i j => raw16577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16577step0 raw16577; decide +kernel
      have hl : raw16577step0Labels = raw16577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16577 raw16577Labels permutation346 hz
    mixedMoment B raw16577step0 raw16577step0Labels = mixedMoment B raw16577step1 raw16577step1Labels := by
      have ha : raw16577step1 = (fun i j => raw16577step0 (permutation122 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16577step1 raw16577step0; decide +kernel
      have hl : raw16577step1Labels = raw16577step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16577step0 raw16577step0Labels permutation122 permutation3
    _ = mixedMoment B node2608 node2608Labels := by rfl

def raw16578 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw16578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16578 raw16578Labels = mixedMoment B node3699 node3699Labels := by
  calc
    mixedMoment B raw16578 raw16578Labels = mixedMoment B raw16578step0 raw16578step0Labels := by
      have hz : ∀ j, raw16578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16578step0 = (fun i j => raw16578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16578step0 raw16578; decide +kernel
      have hl : raw16578step0Labels = raw16578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16578 raw16578Labels permutation346 hz
    mixedMoment B raw16578step0 raw16578step0Labels = mixedMoment B raw16578step1 raw16578step1Labels := by
      have ha : raw16578step1 = (fun i j => raw16578step0 (permutation87 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16578step1 raw16578step0; decide +kernel
      have hl : raw16578step1Labels = raw16578step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16578step0 raw16578step0Labels permutation87 permutation3
    mixedMoment B raw16578step1 raw16578step1Labels = mixedMoment B raw16578step2 raw16578step2Labels := by
      have ha : raw16578step2 = -raw16578step1 := by apply Matrix.ext; change ∀ i j, raw16578step2 i j = -(raw16578step1 i j); unfold raw16578step2 raw16578step1; decide +kernel
      have hl : raw16578step2Labels = raw16578step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3699 node3699Labels := by rfl

def raw16579 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16579 raw16579Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw16579 raw16579Labels = mixedMoment B raw16579step0 raw16579step0Labels := by
      have ha : raw16579step0 = (fun i j => raw16579 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16579step0 raw16579; decide +kernel
      have hl : raw16579step0Labels = raw16579Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16579 raw16579Labels permutation152 permutation6
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw16580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16580 raw16580Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw16580 raw16580Labels = mixedMoment B raw16580step0 raw16580step0Labels := by
      have hz : ∀ j, raw16580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16580step0 = (fun i j => raw16580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16580step0 raw16580; decide +kernel
      have hl : raw16580step0Labels = raw16580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16580 raw16580Labels permutation346 hz
    mixedMoment B raw16580step0 raw16580step0Labels = mixedMoment B raw16580step1 raw16580step1Labels := by
      have ha : raw16580step1 = (fun i j => raw16580step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16580step1 raw16580step0; decide +kernel
      have hl : raw16580step1Labels = raw16580step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16580step0 raw16580step0Labels permutation32 permutation6
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw16581 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw16581step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16581step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16581 raw16581Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw16581 raw16581Labels = mixedMoment B raw16581step0 raw16581step0Labels := by
      have hz : ∀ j, raw16581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16581step0 = (fun i j => raw16581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16581step0 raw16581; decide +kernel
      have hl : raw16581step0Labels = raw16581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16581 raw16581Labels permutation434 hz
    mixedMoment B raw16581step0 raw16581step0Labels = mixedMoment B raw16581step1 raw16581step1Labels := by
      have hz : ∀ j, raw16581step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16581step1 = (fun i j => raw16581step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16581step1 raw16581step0; decide +kernel
      have hl : raw16581step1Labels = raw16581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16581step0 raw16581step0Labels permutation80 hz
    mixedMoment B raw16581step1 raw16581step1Labels = mixedMoment B raw16581step2 raw16581step2Labels := by
      have ha : raw16581step2 = (fun i j => raw16581step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16581step2 raw16581step1; decide +kernel
      have hl : raw16581step2Labels = raw16581step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16581step1 raw16581step1Labels permutation8 permutation6
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw16582 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16582 raw16582Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw16582 raw16582Labels = mixedMoment B raw16582step0 raw16582step0Labels := by
      have hz : ∀ j, raw16582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16582step0 = (fun i j => raw16582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16582step0 raw16582; decide +kernel
      have hl : raw16582step0Labels = raw16582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16582 raw16582Labels permutation346 hz
    mixedMoment B raw16582step0 raw16582step0Labels = mixedMoment B raw16582step1 raw16582step1Labels := by
      have ha : raw16582step1 = (fun i j => raw16582step0 (permutation109 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16582step1 raw16582step0; decide +kernel
      have hl : raw16582step1Labels = raw16582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16582step0 raw16582step0Labels permutation109 permutation3
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw16583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16583Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16583step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16583step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16583step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16583step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16583 raw16583Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw16583 raw16583Labels = mixedMoment B raw16583step0 raw16583step0Labels := by
      have hz : ∀ j, raw16583 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16583step0 = (fun i j => raw16583 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16583step0 raw16583; decide +kernel
      have hl : raw16583step0Labels = raw16583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16583 raw16583Labels permutation434 hz
    mixedMoment B raw16583step0 raw16583step0Labels = mixedMoment B raw16583step1 raw16583step1Labels := by
      have hz : ∀ j, raw16583step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16583step1 = (fun i j => raw16583step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16583step1 raw16583step0; decide +kernel
      have hl : raw16583step1Labels = raw16583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16583step0 raw16583step0Labels permutation80 hz
    mixedMoment B raw16583step1 raw16583step1Labels = mixedMoment B raw16583step2 raw16583step2Labels := by
      have ha : raw16583step2 = (fun i j => raw16583step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16583step2 raw16583step1; decide +kernel
      have hl : raw16583step2Labels = raw16583step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16583step1 raw16583step1Labels permutation8 permutation7
    mixedMoment B raw16583step2 raw16583step2Labels = mixedMoment B raw16583step3 raw16583step3Labels := by
      have ha : raw16583step3 = raw16583step2 := by apply Matrix.ext; unfold raw16583step3 raw16583step2; decide +kernel
      have hl : raw16583step2Labels = labelEmbedding1 ∘ raw16583step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16583step2 raw16583step2Labels raw16583step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw16584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16584Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16584step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16584step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16584step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16584step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16584step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16584step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16584 raw16584Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw16584 raw16584Labels = mixedMoment B raw16584step0 raw16584step0Labels := by
      have hz : ∀ j, raw16584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16584step0 = (fun i j => raw16584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16584step0 raw16584; decide +kernel
      have hl : raw16584step0Labels = raw16584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16584 raw16584Labels permutation346 hz
    mixedMoment B raw16584step0 raw16584step0Labels = mixedMoment B raw16584step1 raw16584step1Labels := by
      have ha : raw16584step1 = (fun i j => raw16584step0 (permutation109 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16584step1 raw16584step0; decide +kernel
      have hl : raw16584step1Labels = raw16584step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16584step0 raw16584step0Labels permutation109 permutation5
    mixedMoment B raw16584step1 raw16584step1Labels = mixedMoment B raw16584step2 raw16584step2Labels := by
      have ha : raw16584step2 = -raw16584step1 := by apply Matrix.ext; change ∀ i j, raw16584step2 i j = -(raw16584step1 i j); unfold raw16584step2 raw16584step1; decide +kernel
      have hl : raw16584step2Labels = raw16584step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16584step2 raw16584step2Labels = mixedMoment B raw16584step3 raw16584step3Labels := by
      have ha : raw16584step3 = raw16584step2 := by apply Matrix.ext; unfold raw16584step3 raw16584step2; decide +kernel
      have hl : raw16584step2Labels = labelEmbedding1 ∘ raw16584step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16584step2 raw16584step2Labels raw16584step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw16585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16585Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16585step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16585step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16585step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16585step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16585step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16585 raw16585Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw16585 raw16585Labels = mixedMoment B raw16585step0 raw16585step0Labels := by
      have hz : ∀ j, raw16585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16585step0 = (fun i j => raw16585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16585step0 raw16585; decide +kernel
      have hl : raw16585step0Labels = raw16585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16585 raw16585Labels permutation346 hz
    mixedMoment B raw16585step0 raw16585step0Labels = mixedMoment B raw16585step1 raw16585step1Labels := by
      have ha : raw16585step1 = (fun i j => raw16585step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16585step1 raw16585step0; decide +kernel
      have hl : raw16585step1Labels = raw16585step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16585step0 raw16585step0Labels permutation151 permutation7
    mixedMoment B raw16585step1 raw16585step1Labels = mixedMoment B raw16585step2 raw16585step2Labels := by
      have ha : raw16585step2 = -raw16585step1 := by apply Matrix.ext; change ∀ i j, raw16585step2 i j = -(raw16585step1 i j); unfold raw16585step2 raw16585step1; decide +kernel
      have hl : raw16585step2Labels = raw16585step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16585step2 raw16585step2Labels = mixedMoment B raw16585step3 raw16585step3Labels := by
      have ha : raw16585step3 = raw16585step2 := by apply Matrix.ext; unfold raw16585step3 raw16585step2; decide +kernel
      have hl : raw16585step2Labels = labelEmbedding1 ∘ raw16585step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16585step2 raw16585step2Labels raw16585step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

def raw16586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16586Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16586step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw16586step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16586step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16586step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16586step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16586 raw16586Labels = mixedMoment B node2875 node2875Labels := by
  calc
    mixedMoment B raw16586 raw16586Labels = mixedMoment B raw16586step0 raw16586step0Labels := by
      have hz : ∀ j, raw16586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16586step0 = (fun i j => raw16586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16586step0 raw16586; decide +kernel
      have hl : raw16586step0Labels = raw16586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16586 raw16586Labels permutation346 hz
    mixedMoment B raw16586step0 raw16586step0Labels = mixedMoment B raw16586step1 raw16586step1Labels := by
      have ha : raw16586step1 = (fun i j => raw16586step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16586step1 raw16586step0; decide +kernel
      have hl : raw16586step1Labels = raw16586step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16586step0 raw16586step0Labels permutation49 permutation5
    mixedMoment B raw16586step1 raw16586step1Labels = mixedMoment B raw16586step2 raw16586step2Labels := by
      have ha : raw16586step2 = -raw16586step1 := by apply Matrix.ext; change ∀ i j, raw16586step2 i j = -(raw16586step1 i j); unfold raw16586step2 raw16586step1; decide +kernel
      have hl : raw16586step2Labels = raw16586step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16586step2 raw16586step2Labels = mixedMoment B raw16586step3 raw16586step3Labels := by
      have ha : raw16586step3 = raw16586step2 := by apply Matrix.ext; unfold raw16586step3 raw16586step2; decide +kernel
      have hl : raw16586step2Labels = labelEmbedding1 ∘ raw16586step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16586step2 raw16586step2Labels raw16586step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2875 node2875Labels := by rfl

def raw16587 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16587Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16587step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16587step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16587step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16587step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16587 raw16587Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw16587 raw16587Labels = mixedMoment B raw16587step0 raw16587step0Labels := by
      have hz : ∀ j, raw16587 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16587step0 = (fun i j => raw16587 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16587step0 raw16587; decide +kernel
      have hl : raw16587step0Labels = raw16587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16587 raw16587Labels permutation434 hz
    mixedMoment B raw16587step0 raw16587step0Labels = mixedMoment B raw16587step1 raw16587step1Labels := by
      have hz : ∀ j, raw16587step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16587step1 = (fun i j => raw16587step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16587step1 raw16587step0; decide +kernel
      have hl : raw16587step1Labels = raw16587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16587step0 raw16587step0Labels permutation80 hz
    mixedMoment B raw16587step1 raw16587step1Labels = mixedMoment B raw16587step2 raw16587step2Labels := by
      have ha : raw16587step2 = (fun i j => raw16587step1 (permutation19 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16587step2 raw16587step1; decide +kernel
      have hl : raw16587step2Labels = raw16587step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16587step1 raw16587step1Labels permutation19 permutation5
    mixedMoment B raw16587step2 raw16587step2Labels = mixedMoment B raw16587step3 raw16587step3Labels := by
      have ha : raw16587step3 = raw16587step2 := by apply Matrix.ext; unfold raw16587step3 raw16587step2; decide +kernel
      have hl : raw16587step2Labels = labelEmbedding1 ∘ raw16587step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16587step2 raw16587step2Labels raw16587step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw16588 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16588Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16588step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw16588step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16588step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16588step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16588 raw16588Labels = mixedMoment B node3385 node3385Labels := by
  calc
    mixedMoment B raw16588 raw16588Labels = mixedMoment B raw16588step0 raw16588step0Labels := by
      have hz : ∀ j, raw16588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16588step0 = (fun i j => raw16588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16588step0 raw16588; decide +kernel
      have hl : raw16588step0Labels = raw16588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16588 raw16588Labels permutation346 hz
    mixedMoment B raw16588step0 raw16588step0Labels = mixedMoment B raw16588step1 raw16588step1Labels := by
      have ha : raw16588step1 = (fun i j => raw16588step0 (permutation109 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16588step1 raw16588step0; decide +kernel
      have hl : raw16588step1Labels = raw16588step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16588step0 raw16588step0Labels permutation109 permutation5
    mixedMoment B raw16588step1 raw16588step1Labels = mixedMoment B raw16588step2 raw16588step2Labels := by
      have ha : raw16588step2 = -raw16588step1 := by apply Matrix.ext; change ∀ i j, raw16588step2 i j = -(raw16588step1 i j); unfold raw16588step2 raw16588step1; decide +kernel
      have hl : raw16588step2Labels = raw16588step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16588step2 raw16588step2Labels = mixedMoment B raw16588step3 raw16588step3Labels := by
      have ha : raw16588step3 = raw16588step2 := by apply Matrix.ext; unfold raw16588step3 raw16588step2; decide +kernel
      have hl : raw16588step2Labels = labelEmbedding1 ∘ raw16588step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16588step2 raw16588step2Labels raw16588step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3385 node3385Labels := by rfl

def raw16589 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16589Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16589step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16589step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16589 raw16589Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw16589 raw16589Labels = mixedMoment B raw16589step0 raw16589step0Labels := by
      have hz : ∀ j, raw16589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16589step0 = (fun i j => raw16589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16589step0 raw16589; decide +kernel
      have hl : raw16589step0Labels = raw16589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16589 raw16589Labels permutation346 hz
    mixedMoment B raw16589step0 raw16589step0Labels = mixedMoment B raw16589step1 raw16589step1Labels := by
      have ha : raw16589step1 = (fun i j => raw16589step0 (permutation67 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16589step1 raw16589step0; decide +kernel
      have hl : raw16589step1Labels = raw16589step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16589step0 raw16589step0Labels permutation67 permutation5
    mixedMoment B raw16589step1 raw16589step1Labels = mixedMoment B raw16589step2 raw16589step2Labels := by
      have ha : raw16589step2 = raw16589step1 := by apply Matrix.ext; unfold raw16589step2 raw16589step1; decide +kernel
      have hl : raw16589step1Labels = labelEmbedding1 ∘ raw16589step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16589step1 raw16589step1Labels raw16589step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw16590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16590Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16590step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16590step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16590step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16590step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16590step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16590 raw16590Labels = mixedMoment B node2876 node2876Labels := by
  calc
    mixedMoment B raw16590 raw16590Labels = mixedMoment B raw16590step0 raw16590step0Labels := by
      have hz : ∀ j, raw16590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16590step0 = (fun i j => raw16590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16590step0 raw16590; decide +kernel
      have hl : raw16590step0Labels = raw16590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16590 raw16590Labels permutation346 hz
    mixedMoment B raw16590step0 raw16590step0Labels = mixedMoment B raw16590step1 raw16590step1Labels := by
      have ha : raw16590step1 = (fun i j => raw16590step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16590step1 raw16590step0; decide +kernel
      have hl : raw16590step1Labels = raw16590step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16590step0 raw16590step0Labels permutation48 permutation5
    mixedMoment B raw16590step1 raw16590step1Labels = mixedMoment B raw16590step2 raw16590step2Labels := by
      have ha : raw16590step2 = -raw16590step1 := by apply Matrix.ext; change ∀ i j, raw16590step2 i j = -(raw16590step1 i j); unfold raw16590step2 raw16590step1; decide +kernel
      have hl : raw16590step2Labels = raw16590step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16590step2 raw16590step2Labels = mixedMoment B raw16590step3 raw16590step3Labels := by
      have ha : raw16590step3 = raw16590step2 := by apply Matrix.ext; unfold raw16590step3 raw16590step2; decide +kernel
      have hl : raw16590step2Labels = labelEmbedding1 ∘ raw16590step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16590step2 raw16590step2Labels raw16590step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2876 node2876Labels := by rfl

def raw16591 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16591Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16591step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16591step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16591step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16591step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16591step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16591 raw16591Labels = mixedMoment B node3386 node3386Labels := by
  calc
    mixedMoment B raw16591 raw16591Labels = mixedMoment B raw16591step0 raw16591step0Labels := by
      have hz : ∀ j, raw16591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16591step0 = (fun i j => raw16591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16591step0 raw16591; decide +kernel
      have hl : raw16591step0Labels = raw16591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16591 raw16591Labels permutation346 hz
    mixedMoment B raw16591step0 raw16591step0Labels = mixedMoment B raw16591step1 raw16591step1Labels := by
      have ha : raw16591step1 = (fun i j => raw16591step0 (permutation108 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16591step1 raw16591step0; decide +kernel
      have hl : raw16591step1Labels = raw16591step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16591step0 raw16591step0Labels permutation108 permutation5
    mixedMoment B raw16591step1 raw16591step1Labels = mixedMoment B raw16591step2 raw16591step2Labels := by
      have ha : raw16591step2 = -raw16591step1 := by apply Matrix.ext; change ∀ i j, raw16591step2 i j = -(raw16591step1 i j); unfold raw16591step2 raw16591step1; decide +kernel
      have hl : raw16591step2Labels = raw16591step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16591step2 raw16591step2Labels = mixedMoment B raw16591step3 raw16591step3Labels := by
      have ha : raw16591step3 = raw16591step2 := by apply Matrix.ext; unfold raw16591step3 raw16591step2; decide +kernel
      have hl : raw16591step2Labels = labelEmbedding1 ∘ raw16591step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16591step2 raw16591step2Labels raw16591step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3386 node3386Labels := by rfl

def raw16592 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16592step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16592 raw16592Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw16592 raw16592Labels = mixedMoment B raw16592step0 raw16592step0Labels := by
      have hz : ∀ j, raw16592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16592step0 = (fun i j => raw16592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16592step0 raw16592; decide +kernel
      have hl : raw16592step0Labels = raw16592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16592 raw16592Labels permutation346 hz
    mixedMoment B raw16592step0 raw16592step0Labels = mixedMoment B raw16592step1 raw16592step1Labels := by
      have ha : raw16592step1 = (fun i j => raw16592step0 (permutation91 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16592step1 raw16592step0; decide +kernel
      have hl : raw16592step1Labels = raw16592step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16592step0 raw16592step0Labels permutation91 permutation5
    mixedMoment B raw16592step1 raw16592step1Labels = mixedMoment B raw16592step2 raw16592step2Labels := by
      have ha : raw16592step2 = raw16592step1 := by apply Matrix.ext; unfold raw16592step2 raw16592step1; decide +kernel
      have hl : raw16592step1Labels = labelEmbedding1 ∘ raw16592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16592step1 raw16592step1Labels raw16592step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3772 node3772Labels := by rfl

def raw16593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16593step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16593step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16593step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16593 raw16593Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw16593 raw16593Labels = mixedMoment B raw16593step0 raw16593step0Labels := by
      have hz : ∀ j, raw16593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16593step0 = (fun i j => raw16593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16593step0 raw16593; decide +kernel
      have hl : raw16593step0Labels = raw16593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16593 raw16593Labels permutation346 hz
    mixedMoment B raw16593step0 raw16593step0Labels = mixedMoment B raw16593step1 raw16593step1Labels := by
      have ha : raw16593step1 = (fun i j => raw16593step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16593step1 raw16593step0; decide +kernel
      have hl : raw16593step1Labels = raw16593step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16593step0 raw16593step0Labels permutation46 permutation5
    mixedMoment B raw16593step1 raw16593step1Labels = mixedMoment B raw16593step2 raw16593step2Labels := by
      have ha : raw16593step2 = -raw16593step1 := by apply Matrix.ext; change ∀ i j, raw16593step2 i j = -(raw16593step1 i j); unfold raw16593step2 raw16593step1; decide +kernel
      have hl : raw16593step2Labels = raw16593step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16593step2 raw16593step2Labels = mixedMoment B raw16593step3 raw16593step3Labels := by
      have ha : raw16593step3 = raw16593step2 := by apply Matrix.ext; unfold raw16593step3 raw16593step2; decide +kernel
      have hl : raw16593step2Labels = labelEmbedding1 ∘ raw16593step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16593step2 raw16593step2Labels raw16593step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2885 node2885Labels := by rfl

def raw16594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw16594step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw16594step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16594step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw16594step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16594 raw16594Labels = mixedMoment B node4030 node4030Labels := by
  calc
    mixedMoment B raw16594 raw16594Labels = mixedMoment B raw16594step0 raw16594step0Labels := by
      have hz : ∀ j, raw16594 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16594step0 = (fun i j => raw16594 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16594step0 raw16594; decide +kernel
      have hl : raw16594step0Labels = raw16594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16594 raw16594Labels permutation434 hz
    mixedMoment B raw16594step0 raw16594step0Labels = mixedMoment B raw16594step1 raw16594step1Labels := by
      have hz : ∀ j, raw16594step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16594step1 = (fun i j => raw16594step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16594step1 raw16594step0; decide +kernel
      have hl : raw16594step1Labels = raw16594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16594step0 raw16594step0Labels permutation80 hz
    mixedMoment B raw16594step1 raw16594step1Labels = mixedMoment B raw16594step2 raw16594step2Labels := by
      have ha : raw16594step2 = (fun i j => raw16594step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16594step2 raw16594step1; decide +kernel
      have hl : raw16594step2Labels = raw16594step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16594step1 raw16594step1Labels permutation29 permutation5
    mixedMoment B raw16594step2 raw16594step2Labels = mixedMoment B raw16594step3 raw16594step3Labels := by
      have ha : raw16594step3 = raw16594step2 := by apply Matrix.ext; unfold raw16594step3 raw16594step2; decide +kernel
      have hl : raw16594step2Labels = labelEmbedding1 ∘ raw16594step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16594step2 raw16594step2Labels raw16594step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4030 node4030Labels := by rfl

def raw16595 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16595step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16595step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16595step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16595step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16595step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16595 raw16595Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw16595 raw16595Labels = mixedMoment B raw16595step0 raw16595step0Labels := by
      have hz : ∀ j, raw16595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16595step0 = (fun i j => raw16595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16595step0 raw16595; decide +kernel
      have hl : raw16595step0Labels = raw16595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16595 raw16595Labels permutation346 hz
    mixedMoment B raw16595step0 raw16595step0Labels = mixedMoment B raw16595step1 raw16595step1Labels := by
      have ha : raw16595step1 = (fun i j => raw16595step0 (permutation106 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16595step1 raw16595step0; decide +kernel
      have hl : raw16595step1Labels = raw16595step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16595step0 raw16595step0Labels permutation106 permutation5
    mixedMoment B raw16595step1 raw16595step1Labels = mixedMoment B raw16595step2 raw16595step2Labels := by
      have ha : raw16595step2 = -raw16595step1 := by apply Matrix.ext; change ∀ i j, raw16595step2 i j = -(raw16595step1 i j); unfold raw16595step2 raw16595step1; decide +kernel
      have hl : raw16595step2Labels = raw16595step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16595step2 raw16595step2Labels = mixedMoment B raw16595step3 raw16595step3Labels := by
      have ha : raw16595step3 = raw16595step2 := by apply Matrix.ext; unfold raw16595step3 raw16595step2; decide +kernel
      have hl : raw16595step2Labels = labelEmbedding1 ∘ raw16595step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16595step2 raw16595step2Labels raw16595step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3395 node3395Labels := by rfl

def raw16596 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16596 raw16596Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw16596 raw16596Labels = mixedMoment B raw16596step0 raw16596step0Labels := by
      have hz : ∀ j, raw16596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16596step0 = (fun i j => raw16596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16596step0 raw16596; decide +kernel
      have hl : raw16596step0Labels = raw16596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16596 raw16596Labels permutation434 hz
    mixedMoment B raw16596step0 raw16596step0Labels = mixedMoment B raw16596step1 raw16596step1Labels := by
      have hz : ∀ j, raw16596step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16596step1 = (fun i j => raw16596step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16596step1 raw16596step0; decide +kernel
      have hl : raw16596step1Labels = raw16596step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16596step0 raw16596step0Labels permutation80 hz
    mixedMoment B raw16596step1 raw16596step1Labels = mixedMoment B raw16596step2 raw16596step2Labels := by
      have ha : raw16596step2 = (fun i j => raw16596step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16596step2 raw16596step1; decide +kernel
      have hl : raw16596step2Labels = raw16596step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16596step1 raw16596step1Labels permutation24 permutation2
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw16597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16597 raw16597Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw16597 raw16597Labels = mixedMoment B raw16597step0 raw16597step0Labels := by
      have hz : ∀ j, raw16597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16597step0 = (fun i j => raw16597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16597step0 raw16597; decide +kernel
      have hl : raw16597step0Labels = raw16597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16597 raw16597Labels permutation346 hz
    mixedMoment B raw16597step0 raw16597step0Labels = mixedMoment B raw16597step1 raw16597step1Labels := by
      have ha : raw16597step1 = (fun i j => raw16597step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16597step1 raw16597step0; decide +kernel
      have hl : raw16597step1Labels = raw16597step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16597step0 raw16597step0Labels permutation126 permutation2
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw16598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16598Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16598step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16598 raw16598Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw16598 raw16598Labels = mixedMoment B raw16598step0 raw16598step0Labels := by
      have hz : ∀ j, raw16598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16598step0 = (fun i j => raw16598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16598step0 raw16598; decide +kernel
      have hl : raw16598step0Labels = raw16598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16598 raw16598Labels permutation346 hz
    mixedMoment B raw16598step0 raw16598step0Labels = mixedMoment B raw16598step1 raw16598step1Labels := by
      have ha : raw16598step1 = (fun i j => raw16598step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16598step1 raw16598step0; decide +kernel
      have hl : raw16598step1Labels = raw16598step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16598step0 raw16598step0Labels permutation150 permutation2
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw16599 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16599 raw16599Labels = mixedMoment B node2871 node2871Labels := by
  calc
    mixedMoment B raw16599 raw16599Labels = mixedMoment B raw16599step0 raw16599step0Labels := by
      have hz : ∀ j, raw16599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16599step0 = (fun i j => raw16599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16599step0 raw16599; decide +kernel
      have hl : raw16599step0Labels = raw16599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16599 raw16599Labels permutation346 hz
    mixedMoment B raw16599step0 raw16599step0Labels = mixedMoment B raw16599step1 raw16599step1Labels := by
      have ha : raw16599step1 = (fun i j => raw16599step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16599step1 raw16599step0; decide +kernel
      have hl : raw16599step1Labels = raw16599step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16599step0 raw16599step0Labels permutation123 permutation2
    _ = mixedMoment B node2871 node2871Labels := by rfl

def raw16600 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16600 raw16600Labels = mixedMoment B node2873 node2873Labels := by
  calc
    mixedMoment B raw16600 raw16600Labels = mixedMoment B raw16600step0 raw16600step0Labels := by
      have hz : ∀ j, raw16600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16600step0 = (fun i j => raw16600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16600step0 raw16600; decide +kernel
      have hl : raw16600step0Labels = raw16600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16600 raw16600Labels permutation346 hz
    mixedMoment B raw16600step0 raw16600step0Labels = mixedMoment B raw16600step1 raw16600step1Labels := by
      have ha : raw16600step1 = (fun i j => raw16600step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16600step1 raw16600step0; decide +kernel
      have hl : raw16600step1Labels = raw16600step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16600step0 raw16600step0Labels permutation123 permutation2
    _ = mixedMoment B node2873 node2873Labels := by rfl

def raw16601 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16601 raw16601Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw16601 raw16601Labels = mixedMoment B raw16601step0 raw16601step0Labels := by
      have hz : ∀ j, raw16601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16601step0 = (fun i j => raw16601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16601step0 raw16601; decide +kernel
      have hl : raw16601step0Labels = raw16601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16601 raw16601Labels permutation346 hz
    mixedMoment B raw16601step0 raw16601step0Labels = mixedMoment B raw16601step1 raw16601step1Labels := by
      have ha : raw16601step1 = (fun i j => raw16601step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16601step1 raw16601step0; decide +kernel
      have hl : raw16601step1Labels = raw16601step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16601step0 raw16601step0Labels permutation123 permutation2
    _ = mixedMoment B node3044 node3044Labels := by rfl

def raw16602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16602step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16602step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16602step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16602step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16602 raw16602Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw16602 raw16602Labels = mixedMoment B raw16602step0 raw16602step0Labels := by
      have hz : ∀ j, raw16602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16602step0 = (fun i j => raw16602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16602step0 raw16602; decide +kernel
      have hl : raw16602step0Labels = raw16602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16602 raw16602Labels permutation346 hz
    mixedMoment B raw16602step0 raw16602step0Labels = mixedMoment B raw16602step1 raw16602step1Labels := by
      have ha : raw16602step1 = (fun i j => raw16602step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16602step1 raw16602step0; decide +kernel
      have hl : raw16602step1Labels = raw16602step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16602step0 raw16602step0Labels permutation62 permutation5
    mixedMoment B raw16602step1 raw16602step1Labels = mixedMoment B raw16602step2 raw16602step2Labels := by
      have ha : raw16602step2 = -raw16602step1 := by apply Matrix.ext; change ∀ i j, raw16602step2 i j = -(raw16602step1 i j); unfold raw16602step2 raw16602step1; decide +kernel
      have hl : raw16602step2Labels = raw16602step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16602step2 raw16602step2Labels = mixedMoment B raw16602step3 raw16602step3Labels := by
      have ha : raw16602step3 = raw16602step2 := by apply Matrix.ext; unfold raw16602step3 raw16602step2; decide +kernel
      have hl : raw16602step2Labels = labelEmbedding8 ∘ raw16602step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16602step2 raw16602step2Labels raw16602step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw16603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16603step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16603 raw16603Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw16603 raw16603Labels = mixedMoment B raw16603step0 raw16603step0Labels := by
      have ha : raw16603step0 = (fun i j => raw16603 (permutation670 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16603step0 raw16603; decide +kernel
      have hl : raw16603step0Labels = raw16603Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16603 raw16603Labels permutation670 permutation5
    mixedMoment B raw16603step0 raw16603step0Labels = mixedMoment B raw16603step1 raw16603step1Labels := by
      have ha : raw16603step1 = raw16603step0 := by apply Matrix.ext; unfold raw16603step1 raw16603step0; decide +kernel
      have hl : raw16603step0Labels = labelEmbedding8 ∘ raw16603step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16603step0 raw16603step0Labels raw16603step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw16604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16604step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16604 raw16604Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw16604 raw16604Labels = mixedMoment B raw16604step0 raw16604step0Labels := by
      have hz : ∀ j, raw16604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16604step0 = (fun i j => raw16604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16604step0 raw16604; decide +kernel
      have hl : raw16604step0Labels = raw16604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16604 raw16604Labels permutation346 hz
    mixedMoment B raw16604step0 raw16604step0Labels = mixedMoment B raw16604step1 raw16604step1Labels := by
      have ha : raw16604step1 = (fun i j => raw16604step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16604step1 raw16604step0; decide +kernel
      have hl : raw16604step1Labels = raw16604step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16604step0 raw16604step0Labels permutation146 permutation5
    mixedMoment B raw16604step1 raw16604step1Labels = mixedMoment B raw16604step2 raw16604step2Labels := by
      have ha : raw16604step2 = raw16604step1 := by apply Matrix.ext; unfold raw16604step2 raw16604step1; decide +kernel
      have hl : raw16604step1Labels = labelEmbedding8 ∘ raw16604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16604step1 raw16604step1Labels raw16604step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw16605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw16605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw16605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16605step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16605step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16605step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16605 raw16605Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw16605 raw16605Labels = mixedMoment B raw16605step0 raw16605step0Labels := by
      have hz : ∀ j, raw16605 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16605step0 = (fun i j => raw16605 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16605step0 raw16605; decide +kernel
      have hl : raw16605step0Labels = raw16605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16605 raw16605Labels permutation520 hz
    mixedMoment B raw16605step0 raw16605step0Labels = mixedMoment B raw16605step1 raw16605step1Labels := by
      have hz : ∀ j, raw16605step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16605step1 = (fun i j => raw16605step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16605step1 raw16605step0; decide +kernel
      have hl : raw16605step1Labels = raw16605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16605step0 raw16605step0Labels permutation80 hz
    mixedMoment B raw16605step1 raw16605step1Labels = mixedMoment B raw16605step2 raw16605step2Labels := by
      have ha : raw16605step2 = (fun i j => raw16605step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16605step2 raw16605step1; decide +kernel
      have hl : raw16605step2Labels = raw16605step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16605step1 raw16605step1Labels permutation27 permutation5
    mixedMoment B raw16605step2 raw16605step2Labels = mixedMoment B raw16605step3 raw16605step3Labels := by
      have ha : raw16605step3 = raw16605step2 := by apply Matrix.ext; unfold raw16605step3 raw16605step2; decide +kernel
      have hl : raw16605step2Labels = labelEmbedding8 ∘ raw16605step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16605step2 raw16605step2Labels raw16605step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw16606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16606step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16606step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16606step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16606step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16606 raw16606Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw16606 raw16606Labels = mixedMoment B raw16606step0 raw16606step0Labels := by
      have hz : ∀ j, raw16606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16606step0 = (fun i j => raw16606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16606step0 raw16606; decide +kernel
      have hl : raw16606step0Labels = raw16606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16606 raw16606Labels permutation346 hz
    mixedMoment B raw16606step0 raw16606step0Labels = mixedMoment B raw16606step1 raw16606step1Labels := by
      have ha : raw16606step1 = (fun i j => raw16606step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16606step1 raw16606step0; decide +kernel
      have hl : raw16606step1Labels = raw16606step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16606step0 raw16606step0Labels permutation65 permutation4
    mixedMoment B raw16606step1 raw16606step1Labels = mixedMoment B raw16606step2 raw16606step2Labels := by
      have ha : raw16606step2 = -raw16606step1 := by apply Matrix.ext; change ∀ i j, raw16606step2 i j = -(raw16606step1 i j); unfold raw16606step2 raw16606step1; decide +kernel
      have hl : raw16606step2Labels = raw16606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16606step2 raw16606step2Labels = mixedMoment B raw16606step3 raw16606step3Labels := by
      have ha : raw16606step3 = raw16606step2 := by apply Matrix.ext; unfold raw16606step3 raw16606step2; decide +kernel
      have hl : raw16606step2Labels = labelEmbedding7 ∘ raw16606step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16606step2 raw16606step2Labels raw16606step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw16607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16607 raw16607Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw16607 raw16607Labels = mixedMoment B raw16607step0 raw16607step0Labels := by
      have hz : ∀ j, raw16607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16607step0 = (fun i j => raw16607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16607step0 raw16607; decide +kernel
      have hl : raw16607step0Labels = raw16607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16607 raw16607Labels permutation346 hz
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw16608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16608step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16608step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16608step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16608 raw16608Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw16608 raw16608Labels = mixedMoment B raw16608step0 raw16608step0Labels := by
      have ha : raw16608step0 = (fun i j => raw16608 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16608step0 raw16608; decide +kernel
      have hl : raw16608step0Labels = raw16608Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16608 raw16608Labels permutation676 permutation3
    mixedMoment B raw16608step0 raw16608step0Labels = mixedMoment B raw16608step1 raw16608step1Labels := by
      have ha : raw16608step1 = -raw16608step0 := by apply Matrix.ext; change ∀ i j, raw16608step1 i j = -(raw16608step0 i j); unfold raw16608step1 raw16608step0; decide +kernel
      have hl : raw16608step1Labels = raw16608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16608step1 raw16608step1Labels = mixedMoment B raw16608step2 raw16608step2Labels := by
      have ha : raw16608step2 = raw16608step1 := by apply Matrix.ext; unfold raw16608step2 raw16608step1; decide +kernel
      have hl : raw16608step1Labels = labelEmbedding6 ∘ raw16608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16608step1 raw16608step1Labels raw16608step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw16609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16609step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16609step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16609step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16609step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16609 raw16609Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw16609 raw16609Labels = mixedMoment B raw16609step0 raw16609step0Labels := by
      have hz : ∀ j, raw16609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16609step0 = (fun i j => raw16609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16609step0 raw16609; decide +kernel
      have hl : raw16609step0Labels = raw16609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16609 raw16609Labels permutation346 hz
    mixedMoment B raw16609step0 raw16609step0Labels = mixedMoment B raw16609step1 raw16609step1Labels := by
      have ha : raw16609step1 = (fun i j => raw16609step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16609step1 raw16609step0; decide +kernel
      have hl : raw16609step1Labels = raw16609step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16609step0 raw16609step0Labels permutation149 permutation3
    mixedMoment B raw16609step1 raw16609step1Labels = mixedMoment B raw16609step2 raw16609step2Labels := by
      have ha : raw16609step2 = -raw16609step1 := by apply Matrix.ext; change ∀ i j, raw16609step2 i j = -(raw16609step1 i j); unfold raw16609step2 raw16609step1; decide +kernel
      have hl : raw16609step2Labels = raw16609step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16609step2 raw16609step2Labels = mixedMoment B raw16609step3 raw16609step3Labels := by
      have ha : raw16609step3 = raw16609step2 := by apply Matrix.ext; unfold raw16609step3 raw16609step2; decide +kernel
      have hl : raw16609step2Labels = labelEmbedding6 ∘ raw16609step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16609step2 raw16609step2Labels raw16609step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw16610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw16610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw16610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16610 raw16610Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw16610 raw16610Labels = mixedMoment B raw16610step0 raw16610step0Labels := by
      have hz : ∀ j, raw16610 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16610step0 = (fun i j => raw16610 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16610step0 raw16610; decide +kernel
      have hl : raw16610step0Labels = raw16610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16610 raw16610Labels permutation520 hz
    mixedMoment B raw16610step0 raw16610step0Labels = mixedMoment B raw16610step1 raw16610step1Labels := by
      have hz : ∀ j, raw16610step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16610step1 = (fun i j => raw16610step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16610step1 raw16610step0; decide +kernel
      have hl : raw16610step1Labels = raw16610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16610step0 raw16610step0Labels permutation80 hz
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw16611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16611 raw16611Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw16611 raw16611Labels = mixedMoment B raw16611step0 raw16611step0Labels := by
      have hz : ∀ j, raw16611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16611step0 = (fun i j => raw16611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16611step0 raw16611; decide +kernel
      have hl : raw16611step0Labels = raw16611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16611 raw16611Labels permutation346 hz
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw16612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw16612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16612 raw16612Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw16612 raw16612Labels = mixedMoment B raw16612step0 raw16612step0Labels := by
      have ha : raw16612step0 = (fun i j => raw16612 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16612step0 raw16612; decide +kernel
      have hl : raw16612step0Labels = raw16612Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16612 raw16612Labels permutation158 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw16613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16613step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw16613step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw16613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16613 raw16613Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw16613 raw16613Labels = mixedMoment B raw16613step0 raw16613step0Labels := by
      have ha : raw16613step0 = (fun i j => raw16613 (permutation305 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16613step0 raw16613; decide +kernel
      have hl : raw16613step0Labels = raw16613Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16613 raw16613Labels permutation305 permutation5
    mixedMoment B raw16613step0 raw16613step0Labels = mixedMoment B raw16613step1 raw16613step1Labels := by
      have ha : raw16613step1 = -raw16613step0 := by apply Matrix.ext; change ∀ i j, raw16613step1 i j = -(raw16613step0 i j); unfold raw16613step1 raw16613step0; decide +kernel
      have hl : raw16613step1Labels = raw16613step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16613step1 raw16613step1Labels = mixedMoment B raw16613step2 raw16613step2Labels := by
      have ha : raw16613step2 = raw16613step1 := by apply Matrix.ext; unfold raw16613step2 raw16613step1; decide +kernel
      have hl : raw16613step1Labels = labelEmbedding8 ∘ raw16613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16613step1 raw16613step1Labels raw16613step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw16614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16614step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16614step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16614 raw16614Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw16614 raw16614Labels = mixedMoment B raw16614step0 raw16614step0Labels := by
      have ha : raw16614step0 = (fun i j => raw16614 (permutation641 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16614step0 raw16614; decide +kernel
      have hl : raw16614step0Labels = raw16614Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16614 raw16614Labels permutation641 permutation5
    mixedMoment B raw16614step0 raw16614step0Labels = mixedMoment B raw16614step1 raw16614step1Labels := by
      have ha : raw16614step1 = raw16614step0 := by apply Matrix.ext; unfold raw16614step1 raw16614step0; decide +kernel
      have hl : raw16614step0Labels = labelEmbedding8 ∘ raw16614step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16614step0 raw16614step0Labels raw16614step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

def raw16615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw16615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16615step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16615step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16615step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16615step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16615 raw16615Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw16615 raw16615Labels = mixedMoment B raw16615step0 raw16615step0Labels := by
      have hz : ∀ j, raw16615 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16615step0 = (fun i j => raw16615 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16615step0 raw16615; decide +kernel
      have hl : raw16615step0Labels = raw16615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16615 raw16615Labels permutation520 hz
    mixedMoment B raw16615step0 raw16615step0Labels = mixedMoment B raw16615step1 raw16615step1Labels := by
      have ha : raw16615step1 = (fun i j => raw16615step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16615step1 raw16615step0; decide +kernel
      have hl : raw16615step1Labels = raw16615step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16615step0 raw16615step0Labels permutation145 permutation3
    mixedMoment B raw16615step1 raw16615step1Labels = mixedMoment B raw16615step2 raw16615step2Labels := by
      have ha : raw16615step2 = -raw16615step1 := by apply Matrix.ext; change ∀ i j, raw16615step2 i j = -(raw16615step1 i j); unfold raw16615step2 raw16615step1; decide +kernel
      have hl : raw16615step2Labels = raw16615step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16615step2 raw16615step2Labels = mixedMoment B raw16615step3 raw16615step3Labels := by
      have ha : raw16615step3 = raw16615step2 := by apply Matrix.ext; unfold raw16615step3 raw16615step2; decide +kernel
      have hl : raw16615step2Labels = labelEmbedding6 ∘ raw16615step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16615step2 raw16615step2Labels raw16615step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw16616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw16616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16616 raw16616Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw16616 raw16616Labels = mixedMoment B raw16616step0 raw16616step0Labels := by
      have ha : raw16616step0 = (fun i j => raw16616 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16616step0 raw16616; decide +kernel
      have hl : raw16616step0Labels = raw16616Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16616 raw16616Labels permutation158 permutation2
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw16617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16617 raw16617Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw16617 raw16617Labels = mixedMoment B raw16617step0 raw16617step0Labels := by
      have hz : ∀ j, raw16617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16617step0 = (fun i j => raw16617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16617step0 raw16617; decide +kernel
      have hl : raw16617step0Labels = raw16617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16617 raw16617Labels permutation346 hz
    mixedMoment B raw16617step0 raw16617step0Labels = mixedMoment B raw16617step1 raw16617step1Labels := by
      have ha : raw16617step1 = (fun i j => raw16617step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16617step1 raw16617step0; decide +kernel
      have hl : raw16617step1Labels = raw16617step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16617step0 raw16617step0Labels permutation34 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw16618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16618step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw16618step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16618step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw16618step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16618 raw16618Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw16618 raw16618Labels = mixedMoment B raw16618step0 raw16618step0Labels := by
      have hz : ∀ j, raw16618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16618step0 = (fun i j => raw16618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16618step0 raw16618; decide +kernel
      have hl : raw16618step0Labels = raw16618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16618 raw16618Labels permutation346 hz
    mixedMoment B raw16618step0 raw16618step0Labels = mixedMoment B raw16618step1 raw16618step1Labels := by
      have ha : raw16618step1 = (fun i j => raw16618step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16618step1 raw16618step0; decide +kernel
      have hl : raw16618step1Labels = raw16618step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16618step0 raw16618step0Labels permutation56 permutation5
    mixedMoment B raw16618step1 raw16618step1Labels = mixedMoment B raw16618step2 raw16618step2Labels := by
      have ha : raw16618step2 = -raw16618step1 := by apply Matrix.ext; change ∀ i j, raw16618step2 i j = -(raw16618step1 i j); unfold raw16618step2 raw16618step1; decide +kernel
      have hl : raw16618step2Labels = raw16618step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16618step2 raw16618step2Labels = mixedMoment B raw16618step3 raw16618step3Labels := by
      have ha : raw16618step3 = raw16618step2 := by apply Matrix.ext; unfold raw16618step3 raw16618step2; decide +kernel
      have hl : raw16618step2Labels = labelEmbedding8 ∘ raw16618step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16618step2 raw16618step2Labels raw16618step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw16619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16619step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16619step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16619 raw16619Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw16619 raw16619Labels = mixedMoment B raw16619step0 raw16619step0Labels := by
      have ha : raw16619step0 = (fun i j => raw16619 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16619step0 raw16619; decide +kernel
      have hl : raw16619step0Labels = raw16619Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16619 raw16619Labels permutation688 permutation3
    mixedMoment B raw16619step0 raw16619step0Labels = mixedMoment B raw16619step1 raw16619step1Labels := by
      have ha : raw16619step1 = -raw16619step0 := by apply Matrix.ext; change ∀ i j, raw16619step1 i j = -(raw16619step0 i j); unfold raw16619step1 raw16619step0; decide +kernel
      have hl : raw16619step1Labels = raw16619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16619step1 raw16619step1Labels = mixedMoment B raw16619step2 raw16619step2Labels := by
      have ha : raw16619step2 = raw16619step1 := by apply Matrix.ext; unfold raw16619step2 raw16619step1; decide +kernel
      have hl : raw16619step1Labels = labelEmbedding6 ∘ raw16619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16619step1 raw16619step1Labels raw16619step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw16620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16620step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16620step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16620step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16620step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16620 raw16620Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw16620 raw16620Labels = mixedMoment B raw16620step0 raw16620step0Labels := by
      have hz : ∀ j, raw16620 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16620step0 = (fun i j => raw16620 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16620step0 raw16620; decide +kernel
      have hl : raw16620step0Labels = raw16620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16620 raw16620Labels permutation520 hz
    mixedMoment B raw16620step0 raw16620step0Labels = mixedMoment B raw16620step1 raw16620step1Labels := by
      have hz : ∀ j, raw16620step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16620step1 = (fun i j => raw16620step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16620step1 raw16620step0; decide +kernel
      have hl : raw16620step1Labels = raw16620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16620step0 raw16620step0Labels permutation80 hz
    mixedMoment B raw16620step1 raw16620step1Labels = mixedMoment B raw16620step2 raw16620step2Labels := by
      have ha : raw16620step2 = (fun i j => raw16620step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16620step2 raw16620step1; decide +kernel
      have hl : raw16620step2Labels = raw16620step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16620step1 raw16620step1Labels permutation31 permutation3
    mixedMoment B raw16620step2 raw16620step2Labels = mixedMoment B raw16620step3 raw16620step3Labels := by
      have ha : raw16620step3 = -raw16620step2 := by apply Matrix.ext; change ∀ i j, raw16620step3 i j = -(raw16620step2 i j); unfold raw16620step3 raw16620step2; decide +kernel
      have hl : raw16620step3Labels = raw16620step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16620step3 raw16620step3Labels = mixedMoment B raw16620step4 raw16620step4Labels := by
      have ha : raw16620step4 = raw16620step3 := by apply Matrix.ext; unfold raw16620step4 raw16620step3; decide +kernel
      have hl : raw16620step3Labels = labelEmbedding6 ∘ raw16620step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16620step3 raw16620step3Labels raw16620step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw16621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16621step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16621 raw16621Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw16621 raw16621Labels = mixedMoment B raw16621step0 raw16621step0Labels := by
      have hz : ∀ j, raw16621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16621step0 = (fun i j => raw16621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16621step0 raw16621; decide +kernel
      have hl : raw16621step0Labels = raw16621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16621 raw16621Labels permutation346 hz
    mixedMoment B raw16621step0 raw16621step0Labels = mixedMoment B raw16621step1 raw16621step1Labels := by
      have ha : raw16621step1 = (fun i j => raw16621step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16621step1 raw16621step0; decide +kernel
      have hl : raw16621step1Labels = raw16621step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16621step0 raw16621step0Labels permutation35 permutation2
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw16622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16622 raw16622Labels = mixedMoment B node5193 node5193Labels := by
  calc
    mixedMoment B raw16622 raw16622Labels = mixedMoment B raw16622step0 raw16622step0Labels := by
      have hz : ∀ j, raw16622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16622step0 = (fun i j => raw16622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16622step0 raw16622; decide +kernel
      have hl : raw16622step0Labels = raw16622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16622 raw16622Labels permutation346 hz
    _ = mixedMoment B node5193 node5193Labels := by rfl

def raw16623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw16623step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw16623step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16623step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw16623step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16623 raw16623Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw16623 raw16623Labels = mixedMoment B raw16623step0 raw16623step0Labels := by
      have hz : ∀ j, raw16623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16623step0 = (fun i j => raw16623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16623step0 raw16623; decide +kernel
      have hl : raw16623step0Labels = raw16623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16623 raw16623Labels permutation346 hz
    mixedMoment B raw16623step0 raw16623step0Labels = mixedMoment B raw16623step1 raw16623step1Labels := by
      have ha : raw16623step1 = (fun i j => raw16623step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16623step1 raw16623step0; decide +kernel
      have hl : raw16623step1Labels = raw16623step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16623step0 raw16623step0Labels permutation62 permutation5
    mixedMoment B raw16623step1 raw16623step1Labels = mixedMoment B raw16623step2 raw16623step2Labels := by
      have ha : raw16623step2 = -raw16623step1 := by apply Matrix.ext; change ∀ i j, raw16623step2 i j = -(raw16623step1 i j); unfold raw16623step2 raw16623step1; decide +kernel
      have hl : raw16623step2Labels = raw16623step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16623step2 raw16623step2Labels = mixedMoment B raw16623step3 raw16623step3Labels := by
      have ha : raw16623step3 = raw16623step2 := by apply Matrix.ext; unfold raw16623step3 raw16623step2; decide +kernel
      have hl : raw16623step2Labels = labelEmbedding8 ∘ raw16623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16623step2 raw16623step2Labels raw16623step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5125 node5125Labels := by rfl

def raw16624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16624step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16624step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16624step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16624 raw16624Labels = mixedMoment B node5326 node5326Labels := by
  calc
    mixedMoment B raw16624 raw16624Labels = mixedMoment B raw16624step0 raw16624step0Labels := by
      have ha : raw16624step0 = (fun i j => raw16624 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16624step0 raw16624; decide +kernel
      have hl : raw16624step0Labels = raw16624Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16624 raw16624Labels permutation589 permutation3
    mixedMoment B raw16624step0 raw16624step0Labels = mixedMoment B raw16624step1 raw16624step1Labels := by
      have ha : raw16624step1 = -raw16624step0 := by apply Matrix.ext; change ∀ i j, raw16624step1 i j = -(raw16624step0 i j); unfold raw16624step1 raw16624step0; decide +kernel
      have hl : raw16624step1Labels = raw16624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16624step1 raw16624step1Labels = mixedMoment B raw16624step2 raw16624step2Labels := by
      have ha : raw16624step2 = raw16624step1 := by apply Matrix.ext; unfold raw16624step2 raw16624step1; decide +kernel
      have hl : raw16624step1Labels = labelEmbedding6 ∘ raw16624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16624step1 raw16624step1Labels raw16624step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5326 node5326Labels := by rfl

def raw16625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16625step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16625 raw16625Labels = mixedMoment B node5330 node5330Labels := by
  calc
    mixedMoment B raw16625 raw16625Labels = mixedMoment B raw16625step0 raw16625step0Labels := by
      have hz : ∀ j, raw16625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16625step0 = (fun i j => raw16625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16625step0 raw16625; decide +kernel
      have hl : raw16625step0Labels = raw16625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16625 raw16625Labels permutation346 hz
    mixedMoment B raw16625step0 raw16625step0Labels = mixedMoment B raw16625step1 raw16625step1Labels := by
      have ha : raw16625step1 = (fun i j => raw16625step0 (permutation122 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16625step1 raw16625step0; decide +kernel
      have hl : raw16625step1Labels = raw16625step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16625step0 raw16625step0Labels permutation122 permutation5
    mixedMoment B raw16625step1 raw16625step1Labels = mixedMoment B raw16625step2 raw16625step2Labels := by
      have ha : raw16625step2 = raw16625step1 := by apply Matrix.ext; unfold raw16625step2 raw16625step1; decide +kernel
      have hl : raw16625step1Labels = labelEmbedding8 ∘ raw16625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16625step1 raw16625step1Labels raw16625step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5330 node5330Labels := by rfl

def raw16626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw16626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw16626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16626step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16626step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16626step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16626step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16626 raw16626Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw16626 raw16626Labels = mixedMoment B raw16626step0 raw16626step0Labels := by
      have hz : ∀ j, raw16626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16626step0 = (fun i j => raw16626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16626step0 raw16626; decide +kernel
      have hl : raw16626step0Labels = raw16626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16626 raw16626Labels permutation346 hz
    mixedMoment B raw16626step0 raw16626step0Labels = mixedMoment B raw16626step1 raw16626step1Labels := by
      have ha : raw16626step1 = (fun i j => raw16626step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16626step1 raw16626step0; decide +kernel
      have hl : raw16626step1Labels = raw16626step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16626step0 raw16626step0Labels permutation127 permutation3
    mixedMoment B raw16626step1 raw16626step1Labels = mixedMoment B raw16626step2 raw16626step2Labels := by
      have ha : raw16626step2 = -raw16626step1 := by apply Matrix.ext; change ∀ i j, raw16626step2 i j = -(raw16626step1 i j); unfold raw16626step2 raw16626step1; decide +kernel
      have hl : raw16626step2Labels = raw16626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16626step2 raw16626step2Labels = mixedMoment B raw16626step3 raw16626step3Labels := by
      have ha : raw16626step3 = raw16626step2 := by apply Matrix.ext; unfold raw16626step3 raw16626step2; decide +kernel
      have hl : raw16626step2Labels = labelEmbedding6 ∘ raw16626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16626step2 raw16626step2Labels raw16626step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw16627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw16627step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw16627step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16627step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw16627step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16627 raw16627Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw16627 raw16627Labels = mixedMoment B raw16627step0 raw16627step0Labels := by
      have hz : ∀ j, raw16627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16627step0 = (fun i j => raw16627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16627step0 raw16627; decide +kernel
      have hl : raw16627step0Labels = raw16627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16627 raw16627Labels permutation346 hz
    mixedMoment B raw16627step0 raw16627step0Labels = mixedMoment B raw16627step1 raw16627step1Labels := by
      have ha : raw16627step1 = (fun i j => raw16627step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16627step1 raw16627step0; decide +kernel
      have hl : raw16627step1Labels = raw16627step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16627step0 raw16627step0Labels permutation151 permutation3
    mixedMoment B raw16627step1 raw16627step1Labels = mixedMoment B raw16627step2 raw16627step2Labels := by
      have ha : raw16627step2 = -raw16627step1 := by apply Matrix.ext; change ∀ i j, raw16627step2 i j = -(raw16627step1 i j); unfold raw16627step2 raw16627step1; decide +kernel
      have hl : raw16627step2Labels = raw16627step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16627step2 raw16627step2Labels = mixedMoment B raw16627step3 raw16627step3Labels := by
      have ha : raw16627step3 = raw16627step2 := by apply Matrix.ext; unfold raw16627step3 raw16627step2; decide +kernel
      have hl : raw16627step2Labels = labelEmbedding6 ∘ raw16627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16627step2 raw16627step2Labels raw16627step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw16628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw16628step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw16628step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16628step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw16628step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16628 raw16628Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw16628 raw16628Labels = mixedMoment B raw16628step0 raw16628step0Labels := by
      have hz : ∀ j, raw16628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16628step0 = (fun i j => raw16628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16628step0 raw16628; decide +kernel
      have hl : raw16628step0Labels = raw16628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16628 raw16628Labels permutation346 hz
    mixedMoment B raw16628step0 raw16628step0Labels = mixedMoment B raw16628step1 raw16628step1Labels := by
      have ha : raw16628step1 = (fun i j => raw16628step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16628step1 raw16628step0; decide +kernel
      have hl : raw16628step1Labels = raw16628step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16628step0 raw16628step0Labels permutation150 permutation3
    mixedMoment B raw16628step1 raw16628step1Labels = mixedMoment B raw16628step2 raw16628step2Labels := by
      have ha : raw16628step2 = -raw16628step1 := by apply Matrix.ext; change ∀ i j, raw16628step2 i j = -(raw16628step1 i j); unfold raw16628step2 raw16628step1; decide +kernel
      have hl : raw16628step2Labels = raw16628step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16628step2 raw16628step2Labels = mixedMoment B raw16628step3 raw16628step3Labels := by
      have ha : raw16628step3 = raw16628step2 := by apply Matrix.ext; unfold raw16628step3 raw16628step2; decide +kernel
      have hl : raw16628step2Labels = labelEmbedding6 ∘ raw16628step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16628step2 raw16628step2Labels raw16628step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw16629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16629step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16629step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16629step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16629step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16629 raw16629Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw16629 raw16629Labels = mixedMoment B raw16629step0 raw16629step0Labels := by
      have ha : raw16629step0 = (fun i j => raw16629 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16629step0 raw16629; decide +kernel
      have hl : raw16629step0Labels = raw16629Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16629 raw16629Labels permutation688 permutation3
    mixedMoment B raw16629step0 raw16629step0Labels = mixedMoment B raw16629step1 raw16629step1Labels := by
      have ha : raw16629step1 = -raw16629step0 := by apply Matrix.ext; change ∀ i j, raw16629step1 i j = -(raw16629step0 i j); unfold raw16629step1 raw16629step0; decide +kernel
      have hl : raw16629step1Labels = raw16629step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16629step1 raw16629step1Labels = mixedMoment B raw16629step2 raw16629step2Labels := by
      have ha : raw16629step2 = raw16629step1 := by apply Matrix.ext; unfold raw16629step2 raw16629step1; decide +kernel
      have hl : raw16629step1Labels = labelEmbedding6 ∘ raw16629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16629step1 raw16629step1Labels raw16629step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw16630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16630step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16630step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16630 raw16630Labels = mixedMoment B node4750 node4750Labels := by
  calc
    mixedMoment B raw16630 raw16630Labels = mixedMoment B raw16630step0 raw16630step0Labels := by
      have hz : ∀ j, raw16630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16630step0 = (fun i j => raw16630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16630step0 raw16630; decide +kernel
      have hl : raw16630step0Labels = raw16630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16630 raw16630Labels permutation346 hz
    mixedMoment B raw16630step0 raw16630step0Labels = mixedMoment B raw16630step1 raw16630step1Labels := by
      have ha : raw16630step1 = (fun i j => raw16630step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16630step1 raw16630step0; decide +kernel
      have hl : raw16630step1Labels = raw16630step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16630step0 raw16630step0Labels permutation146 permutation5
    mixedMoment B raw16630step1 raw16630step1Labels = mixedMoment B raw16630step2 raw16630step2Labels := by
      have ha : raw16630step2 = raw16630step1 := by apply Matrix.ext; unfold raw16630step2 raw16630step1; decide +kernel
      have hl : raw16630step1Labels = labelEmbedding8 ∘ raw16630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16630step1 raw16630step1Labels raw16630step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4750 node4750Labels := by rfl

def raw16631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw16631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw16631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw16631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16631step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16631step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16631step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16631step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16631step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16631 raw16631Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw16631 raw16631Labels = mixedMoment B raw16631step0 raw16631step0Labels := by
      have hz : ∀ j, raw16631 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16631step0 = (fun i j => raw16631 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16631step0 raw16631; decide +kernel
      have hl : raw16631step0Labels = raw16631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16631 raw16631Labels permutation520 hz
    mixedMoment B raw16631step0 raw16631step0Labels = mixedMoment B raw16631step1 raw16631step1Labels := by
      have hz : ∀ j, raw16631step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16631step1 = (fun i j => raw16631step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16631step1 raw16631step0; decide +kernel
      have hl : raw16631step1Labels = raw16631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16631step0 raw16631step0Labels permutation80 hz
    mixedMoment B raw16631step1 raw16631step1Labels = mixedMoment B raw16631step2 raw16631step2Labels := by
      have ha : raw16631step2 = (fun i j => raw16631step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16631step2 raw16631step1; decide +kernel
      have hl : raw16631step2Labels = raw16631step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16631step1 raw16631step1Labels permutation31 permutation3
    mixedMoment B raw16631step2 raw16631step2Labels = mixedMoment B raw16631step3 raw16631step3Labels := by
      have ha : raw16631step3 = -raw16631step2 := by apply Matrix.ext; change ∀ i j, raw16631step3 i j = -(raw16631step2 i j); unfold raw16631step3 raw16631step2; decide +kernel
      have hl : raw16631step3Labels = raw16631step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16631step3 raw16631step3Labels = mixedMoment B raw16631step4 raw16631step4Labels := by
      have ha : raw16631step4 = raw16631step3 := by apply Matrix.ext; unfold raw16631step4 raw16631step3; decide +kernel
      have hl : raw16631step3Labels = labelEmbedding6 ∘ raw16631step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16631step3 raw16631step3Labels raw16631step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw16632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16632 raw16632Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw16632 raw16632Labels = mixedMoment B raw16632step0 raw16632step0Labels := by
      have hz : ∀ j, raw16632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16632step0 = (fun i j => raw16632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16632step0 raw16632; decide +kernel
      have hl : raw16632step0Labels = raw16632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16632 raw16632Labels permutation346 hz
    mixedMoment B raw16632step0 raw16632step0Labels = mixedMoment B raw16632step1 raw16632step1Labels := by
      have ha : raw16632step1 = (fun i j => raw16632step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16632step1 raw16632step0; decide +kernel
      have hl : raw16632step1Labels = raw16632step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16632step0 raw16632step0Labels permutation56 permutation3
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw16633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16633 raw16633Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw16633 raw16633Labels = mixedMoment B raw16633step0 raw16633step0Labels := by
      have ha : raw16633step0 = (fun i j => raw16633 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16633step0 raw16633; decide +kernel
      have hl : raw16633step0Labels = raw16633Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16633 raw16633Labels permutation684 permutation3
    mixedMoment B raw16633step0 raw16633step0Labels = mixedMoment B raw16633step1 raw16633step1Labels := by
      have ha : raw16633step1 = -raw16633step0 := by apply Matrix.ext; change ∀ i j, raw16633step1 i j = -(raw16633step0 i j); unfold raw16633step1 raw16633step0; decide +kernel
      have hl : raw16633step1Labels = raw16633step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw16634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw16634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw16634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16634 raw16634Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw16634 raw16634Labels = mixedMoment B raw16634step0 raw16634step0Labels := by
      have hz : ∀ j, raw16634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16634step0 = (fun i j => raw16634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16634step0 raw16634; decide +kernel
      have hl : raw16634step0Labels = raw16634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16634 raw16634Labels permutation346 hz
    mixedMoment B raw16634step0 raw16634step0Labels = mixedMoment B raw16634step1 raw16634step1Labels := by
      have ha : raw16634step1 = (fun i j => raw16634step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16634step1 raw16634step0; decide +kernel
      have hl : raw16634step1Labels = raw16634step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16634step0 raw16634step0Labels permutation146 permutation3
    mixedMoment B raw16634step1 raw16634step1Labels = mixedMoment B raw16634step2 raw16634step2Labels := by
      have ha : raw16634step2 = -raw16634step1 := by apply Matrix.ext; change ∀ i j, raw16634step2 i j = -(raw16634step1 i j); unfold raw16634step2 raw16634step1; decide +kernel
      have hl : raw16634step2Labels = raw16634step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3815 node3815Labels := by rfl

def raw16635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw16635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw16635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw16635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16635step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw16635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16635 raw16635Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw16635 raw16635Labels = mixedMoment B raw16635step0 raw16635step0Labels := by
      have hz : ∀ j, raw16635 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16635step0 = (fun i j => raw16635 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16635step0 raw16635; decide +kernel
      have hl : raw16635step0Labels = raw16635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16635 raw16635Labels permutation520 hz
    mixedMoment B raw16635step0 raw16635step0Labels = mixedMoment B raw16635step1 raw16635step1Labels := by
      have hz : ∀ j, raw16635step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16635step1 = (fun i j => raw16635step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16635step1 raw16635step0; decide +kernel
      have hl : raw16635step1Labels = raw16635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16635step0 raw16635step0Labels permutation80 hz
    mixedMoment B raw16635step1 raw16635step1Labels = mixedMoment B raw16635step2 raw16635step2Labels := by
      have ha : raw16635step2 = (fun i j => raw16635step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16635step2 raw16635step1; decide +kernel
      have hl : raw16635step2Labels = raw16635step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16635step1 raw16635step1Labels permutation30 permutation3
    mixedMoment B raw16635step2 raw16635step2Labels = mixedMoment B raw16635step3 raw16635step3Labels := by
      have ha : raw16635step3 = -raw16635step2 := by apply Matrix.ext; change ∀ i j, raw16635step3 i j = -(raw16635step2 i j); unfold raw16635step3 raw16635step2; decide +kernel
      have hl : raw16635step3Labels = raw16635step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw16636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16636 raw16636Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw16636 raw16636Labels = mixedMoment B raw16636step0 raw16636step0Labels := by
      have hz : ∀ j, raw16636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16636step0 = (fun i j => raw16636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16636step0 raw16636; decide +kernel
      have hl : raw16636step0Labels = raw16636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16636 raw16636Labels permutation346 hz
    mixedMoment B raw16636step0 raw16636step0Labels = mixedMoment B raw16636step1 raw16636step1Labels := by
      have ha : raw16636step1 = (fun i j => raw16636step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16636step1 raw16636step0; decide +kernel
      have hl : raw16636step1Labels = raw16636step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16636step0 raw16636step0Labels permutation49 permutation6
    mixedMoment B raw16636step1 raw16636step1Labels = mixedMoment B raw16636step2 raw16636step2Labels := by
      have ha : raw16636step2 = -raw16636step1 := by apply Matrix.ext; change ∀ i j, raw16636step2 i j = -(raw16636step1 i j); unfold raw16636step2 raw16636step1; decide +kernel
      have hl : raw16636step2Labels = raw16636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw16637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16637 raw16637Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw16637 raw16637Labels = mixedMoment B raw16637step0 raw16637step0Labels := by
      have hz : ∀ j, raw16637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16637step0 = (fun i j => raw16637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16637step0 raw16637; decide +kernel
      have hl : raw16637step0Labels = raw16637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16637 raw16637Labels permutation346 hz
    mixedMoment B raw16637step0 raw16637step0Labels = mixedMoment B raw16637step1 raw16637step1Labels := by
      have ha : raw16637step1 = (fun i j => raw16637step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16637step1 raw16637step0; decide +kernel
      have hl : raw16637step1Labels = raw16637step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16637step0 raw16637step0Labels permutation32 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw16638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16638 raw16638Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw16638 raw16638Labels = mixedMoment B raw16638step0 raw16638step0Labels := by
      have ha : raw16638step0 = (fun i j => raw16638 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16638step0 raw16638; decide +kernel
      have hl : raw16638step0Labels = raw16638Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16638 raw16638Labels permutation676 permutation3
    mixedMoment B raw16638step0 raw16638step0Labels = mixedMoment B raw16638step1 raw16638step1Labels := by
      have ha : raw16638step1 = -raw16638step0 := by apply Matrix.ext; change ∀ i j, raw16638step1 i j = -(raw16638step0 i j); unfold raw16638step1 raw16638step0; decide +kernel
      have hl : raw16638step1Labels = raw16638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw16639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16639 raw16639Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw16639 raw16639Labels = mixedMoment B raw16639step0 raw16639step0Labels := by
      have hz : ∀ j, raw16639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16639step0 = (fun i j => raw16639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16639step0 raw16639; decide +kernel
      have hl : raw16639step0Labels = raw16639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16639 raw16639Labels permutation346 hz
    mixedMoment B raw16639step0 raw16639step0Labels = mixedMoment B raw16639step1 raw16639step1Labels := by
      have ha : raw16639step1 = (fun i j => raw16639step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16639step1 raw16639step0; decide +kernel
      have hl : raw16639step1Labels = raw16639step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16639step0 raw16639step0Labels permutation149 permutation3
    mixedMoment B raw16639step1 raw16639step1Labels = mixedMoment B raw16639step2 raw16639step2Labels := by
      have ha : raw16639step2 = -raw16639step1 := by apply Matrix.ext; change ∀ i j, raw16639step2 i j = -(raw16639step1 i j); unfold raw16639step2 raw16639step1; decide +kernel
      have hl : raw16639step2Labels = raw16639step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
