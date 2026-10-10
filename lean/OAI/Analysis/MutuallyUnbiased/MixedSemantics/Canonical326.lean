import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41728Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41728step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41728 raw41728Labels = mixedMoment B node2160 node2160Labels := by
  calc
    mixedMoment B raw41728 raw41728Labels = mixedMoment B raw41728step0 raw41728step0Labels := by
      have ha : raw41728step0 = (fun i j => raw41728 (permutation337 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41728step0 raw41728; decide +kernel
      have hl : raw41728step0Labels = raw41728Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41728 raw41728Labels permutation337 permutation4
    mixedMoment B raw41728step0 raw41728step0Labels = mixedMoment B raw41728step1 raw41728step1Labels := by
      have ha : raw41728step1 = -raw41728step0 := by apply Matrix.ext; change ∀ i j, raw41728step1 i j = -(raw41728step0 i j); unfold raw41728step1 raw41728step0; decide +kernel
      have hl : raw41728step1Labels = raw41728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41728step1 raw41728step1Labels = mixedMoment B raw41728step2 raw41728step2Labels := by
      have ha : raw41728step2 = raw41728step1 := by apply Matrix.ext; unfold raw41728step2 raw41728step1; decide +kernel
      have hl : raw41728step1Labels = labelEmbedding1 ∘ raw41728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41728step1 raw41728step1Labels raw41728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2160 node2160Labels := by rfl

def raw41729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41729Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41729 raw41729Labels = mixedMoment B node4667 node4667Labels := by
  calc
    mixedMoment B raw41729 raw41729Labels = mixedMoment B raw41729step0 raw41729step0Labels := by
      have ha : raw41729step0 = (fun i j => raw41729 (permutation345 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41729step0 raw41729; decide +kernel
      have hl : raw41729step0Labels = raw41729Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41729 raw41729Labels permutation345 permutation6
    _ = mixedMoment B node4667 node4667Labels := by rfl

def raw41730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41730Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw41730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41730step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41730 raw41730Labels = mixedMoment B node2179 node2179Labels := by
  calc
    mixedMoment B raw41730 raw41730Labels = mixedMoment B raw41730step0 raw41730step0Labels := by
      have ha : raw41730step0 = (fun i j => raw41730 (permutation313 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41730step0 raw41730; decide +kernel
      have hl : raw41730step0Labels = raw41730Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41730 raw41730Labels permutation313 permutation4
    mixedMoment B raw41730step0 raw41730step0Labels = mixedMoment B raw41730step1 raw41730step1Labels := by
      have ha : raw41730step1 = -raw41730step0 := by apply Matrix.ext; change ∀ i j, raw41730step1 i j = -(raw41730step0 i j); unfold raw41730step1 raw41730step0; decide +kernel
      have hl : raw41730step1Labels = raw41730step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41730step1 raw41730step1Labels = mixedMoment B raw41730step2 raw41730step2Labels := by
      have ha : raw41730step2 = raw41730step1 := by apply Matrix.ext; unfold raw41730step2 raw41730step1; decide +kernel
      have hl : raw41730step1Labels = labelEmbedding1 ∘ raw41730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41730step1 raw41730step1Labels raw41730step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2179 node2179Labels := by rfl

def raw41731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41731Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41731 raw41731Labels = mixedMoment B node4765 node4765Labels := by
  calc
    mixedMoment B raw41731 raw41731Labels = mixedMoment B raw41731step0 raw41731step0Labels := by
      have ha : raw41731step0 = (fun i j => raw41731 (permutation316 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41731step0 raw41731; decide +kernel
      have hl : raw41731step0Labels = raw41731Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41731 raw41731Labels permutation316 permutation6
    _ = mixedMoment B node4765 node4765Labels := by rfl

def raw41732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41732Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41732step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41732step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41732 raw41732Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw41732 raw41732Labels = mixedMoment B raw41732step0 raw41732step0Labels := by
      have ha : raw41732step0 = (fun i j => raw41732 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41732step0 raw41732; decide +kernel
      have hl : raw41732step0Labels = raw41732Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41732 raw41732Labels permutation179 permutation2
    mixedMoment B raw41732step0 raw41732step0Labels = mixedMoment B raw41732step1 raw41732step1Labels := by
      have ha : raw41732step1 = raw41732step0 := by apply Matrix.ext; unfold raw41732step1 raw41732step0; decide +kernel
      have hl : raw41732step0Labels = labelEmbedding1 ∘ raw41732step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41732step0 raw41732step0Labels raw41732step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2219 node2219Labels := by rfl

def raw41733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41733Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41733 raw41733Labels = mixedMoment B node4793 node4793Labels := by
  calc
    mixedMoment B raw41733 raw41733Labels = mixedMoment B raw41733step0 raw41733step0Labels := by
      have ha : raw41733step0 = (fun i j => raw41733 (permutation317 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41733step0 raw41733; decide +kernel
      have hl : raw41733step0Labels = raw41733Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41733 raw41733Labels permutation317 permutation6
    _ = mixedMoment B node4793 node4793Labels := by rfl

def raw41734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41734Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41734 raw41734Labels = mixedMoment B node2160 node2160Labels := by
  calc
    mixedMoment B raw41734 raw41734Labels = mixedMoment B raw41734step0 raw41734step0Labels := by
      have ha : raw41734step0 = (fun i j => raw41734 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41734step0 raw41734; decide +kernel
      have hl : raw41734step0Labels = raw41734Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41734 raw41734Labels permutation180 permutation2
    mixedMoment B raw41734step0 raw41734step0Labels = mixedMoment B raw41734step1 raw41734step1Labels := by
      have ha : raw41734step1 = raw41734step0 := by apply Matrix.ext; unfold raw41734step1 raw41734step0; decide +kernel
      have hl : raw41734step0Labels = labelEmbedding1 ∘ raw41734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41734step0 raw41734step0Labels raw41734step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2160 node2160Labels := by rfl

def raw41735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41735Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw41735step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41735step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41735step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41735step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41735 raw41735Labels = mixedMoment B node4667 node4667Labels := by
  calc
    mixedMoment B raw41735 raw41735Labels = mixedMoment B raw41735step0 raw41735step0Labels := by
      have ha : raw41735step0 = (fun i j => raw41735 (permutation197 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41735step0 raw41735; decide +kernel
      have hl : raw41735step0Labels = raw41735Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41735 raw41735Labels permutation197 permutation7
    mixedMoment B raw41735step0 raw41735step0Labels = mixedMoment B raw41735step1 raw41735step1Labels := by
      have ha : raw41735step1 = -raw41735step0 := by apply Matrix.ext; change ∀ i j, raw41735step1 i j = -(raw41735step0 i j); unfold raw41735step1 raw41735step0; decide +kernel
      have hl : raw41735step1Labels = raw41735step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41735step1 raw41735step1Labels = mixedMoment B raw41735step2 raw41735step2Labels := by
      have ha : raw41735step2 = raw41735step1 := by apply Matrix.ext; unfold raw41735step2 raw41735step1; decide +kernel
      have hl : raw41735step1Labels = labelEmbedding6 ∘ raw41735step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41735step1 raw41735step1Labels raw41735step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4667 node4667Labels := by rfl

def raw41736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41736Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw41736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw41736step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw41736step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41736 raw41736Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw41736 raw41736Labels = mixedMoment B raw41736step0 raw41736step0Labels := by
      have hz : ∀ j, raw41736 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41736step0 = (fun i j => raw41736 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41736step0 raw41736; decide +kernel
      have hl : raw41736step0Labels = raw41736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41736 raw41736Labels permutation520 hz
    mixedMoment B raw41736step0 raw41736step0Labels = mixedMoment B raw41736step1 raw41736step1Labels := by
      have hz : ∀ j, raw41736step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41736step1 = (fun i j => raw41736step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41736step1 raw41736step0; decide +kernel
      have hl : raw41736step1Labels = raw41736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41736step0 raw41736step0Labels permutation104 hz
    mixedMoment B raw41736step1 raw41736step1Labels = mixedMoment B raw41736step2 raw41736step2Labels := by
      have ha : raw41736step2 = (fun i j => raw41736step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41736step2 raw41736step1; decide +kernel
      have hl : raw41736step2Labels = raw41736step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41736step1 raw41736step1Labels permutation10 permutation2
    mixedMoment B raw41736step2 raw41736step2Labels = mixedMoment B raw41736step3 raw41736step3Labels := by
      have ha : raw41736step3 = raw41736step2 := by apply Matrix.ext; unfold raw41736step3 raw41736step2; decide +kernel
      have hl : raw41736step2Labels = labelEmbedding1 ∘ raw41736step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41736step2 raw41736step2Labels raw41736step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw41737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41737Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41737step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw41737step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw41737step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41737step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw41737step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41737 raw41737Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw41737 raw41737Labels = mixedMoment B raw41737step0 raw41737step0Labels := by
      have hz : ∀ j, raw41737 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41737step0 = (fun i j => raw41737 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41737step0 raw41737; decide +kernel
      have hl : raw41737step0Labels = raw41737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41737 raw41737Labels permutation520 hz
    mixedMoment B raw41737step0 raw41737step0Labels = mixedMoment B raw41737step1 raw41737step1Labels := by
      have hz : ∀ j, raw41737step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41737step1 = (fun i j => raw41737step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41737step1 raw41737step0; decide +kernel
      have hl : raw41737step1Labels = raw41737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41737step0 raw41737step0Labels permutation104 hz
    mixedMoment B raw41737step1 raw41737step1Labels = mixedMoment B raw41737step2 raw41737step2Labels := by
      have ha : raw41737step2 = (fun i j => raw41737step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41737step2 raw41737step1; decide +kernel
      have hl : raw41737step2Labels = raw41737step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41737step1 raw41737step1Labels permutation10 permutation2
    mixedMoment B raw41737step2 raw41737step2Labels = mixedMoment B raw41737step3 raw41737step3Labels := by
      have ha : raw41737step3 = raw41737step2 := by apply Matrix.ext; unfold raw41737step3 raw41737step2; decide +kernel
      have hl : raw41737step2Labels = labelEmbedding8 ∘ raw41737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41737step2 raw41737step2Labels raw41737step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw41738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41738Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41738step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41738 raw41738Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw41738 raw41738Labels = mixedMoment B raw41738step0 raw41738step0Labels := by
      have hz : ∀ j, raw41738 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41738step0 = (fun i j => raw41738 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41738step0 raw41738; decide +kernel
      have hl : raw41738step0Labels = raw41738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41738 raw41738Labels permutation434 hz
    mixedMoment B raw41738step0 raw41738step0Labels = mixedMoment B raw41738step1 raw41738step1Labels := by
      have ha : raw41738step1 = (fun i j => raw41738step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41738step1 raw41738step0; decide +kernel
      have hl : raw41738step1Labels = raw41738step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41738step0 raw41738step0Labels permutation38 permutation2
    mixedMoment B raw41738step1 raw41738step1Labels = mixedMoment B raw41738step2 raw41738step2Labels := by
      have ha : raw41738step2 = raw41738step1 := by apply Matrix.ext; unfold raw41738step2 raw41738step1; decide +kernel
      have hl : raw41738step1Labels = labelEmbedding1 ∘ raw41738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41738step1 raw41738step1Labels raw41738step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw41739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41739Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41739step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw41739step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41739step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41739step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41739 raw41739Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw41739 raw41739Labels = mixedMoment B raw41739step0 raw41739step0Labels := by
      have hz : ∀ j, raw41739 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41739step0 = (fun i j => raw41739 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41739step0 raw41739; decide +kernel
      have hl : raw41739step0Labels = raw41739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41739 raw41739Labels permutation434 hz
    mixedMoment B raw41739step0 raw41739step0Labels = mixedMoment B raw41739step1 raw41739step1Labels := by
      have ha : raw41739step1 = (fun i j => raw41739step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41739step1 raw41739step0; decide +kernel
      have hl : raw41739step1Labels = raw41739step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41739step0 raw41739step0Labels permutation53 permutation7
    mixedMoment B raw41739step1 raw41739step1Labels = mixedMoment B raw41739step2 raw41739step2Labels := by
      have ha : raw41739step2 = -raw41739step1 := by apply Matrix.ext; change ∀ i j, raw41739step2 i j = -(raw41739step1 i j); unfold raw41739step2 raw41739step1; decide +kernel
      have hl : raw41739step2Labels = raw41739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41739step2 raw41739step2Labels = mixedMoment B raw41739step3 raw41739step3Labels := by
      have ha : raw41739step3 = raw41739step2 := by apply Matrix.ext; unfold raw41739step3 raw41739step2; decide +kernel
      have hl : raw41739step2Labels = labelEmbedding6 ∘ raw41739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41739step2 raw41739step2Labels raw41739step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw41740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41740Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41740step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41740 raw41740Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw41740 raw41740Labels = mixedMoment B raw41740step0 raw41740step0Labels := by
      have hz : ∀ j, raw41740 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41740step0 = (fun i j => raw41740 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41740step0 raw41740; decide +kernel
      have hl : raw41740step0Labels = raw41740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41740 raw41740Labels permutation434 hz
    mixedMoment B raw41740step0 raw41740step0Labels = mixedMoment B raw41740step1 raw41740step1Labels := by
      have ha : raw41740step1 = (fun i j => raw41740step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41740step1 raw41740step0; decide +kernel
      have hl : raw41740step1Labels = raw41740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41740step0 raw41740step0Labels permutation38 permutation2
    mixedMoment B raw41740step1 raw41740step1Labels = mixedMoment B raw41740step2 raw41740step2Labels := by
      have ha : raw41740step2 = raw41740step1 := by apply Matrix.ext; unfold raw41740step2 raw41740step1; decide +kernel
      have hl : raw41740step1Labels = labelEmbedding1 ∘ raw41740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41740step1 raw41740step1Labels raw41740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw41741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41741Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41741step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41741step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41741step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41741 raw41741Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw41741 raw41741Labels = mixedMoment B raw41741step0 raw41741step0Labels := by
      have hz : ∀ j, raw41741 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41741step0 = (fun i j => raw41741 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41741step0 raw41741; decide +kernel
      have hl : raw41741step0Labels = raw41741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41741 raw41741Labels permutation434 hz
    mixedMoment B raw41741step0 raw41741step0Labels = mixedMoment B raw41741step1 raw41741step1Labels := by
      have ha : raw41741step1 = (fun i j => raw41741step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41741step1 raw41741step0; decide +kernel
      have hl : raw41741step1Labels = raw41741step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41741step0 raw41741step0Labels permutation38 permutation2
    mixedMoment B raw41741step1 raw41741step1Labels = mixedMoment B raw41741step2 raw41741step2Labels := by
      have ha : raw41741step2 = raw41741step1 := by apply Matrix.ext; unfold raw41741step2 raw41741step1; decide +kernel
      have hl : raw41741step1Labels = labelEmbedding8 ∘ raw41741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41741step1 raw41741step1Labels raw41741step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw41742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41742Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41742step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41742 raw41742Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw41742 raw41742Labels = mixedMoment B raw41742step0 raw41742step0Labels := by
      have hz : ∀ j, raw41742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41742step0 = (fun i j => raw41742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41742step0 raw41742; decide +kernel
      have hl : raw41742step0Labels = raw41742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41742 raw41742Labels permutation434 hz
    mixedMoment B raw41742step0 raw41742step0Labels = mixedMoment B raw41742step1 raw41742step1Labels := by
      have ha : raw41742step1 = (fun i j => raw41742step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41742step1 raw41742step0; decide +kernel
      have hl : raw41742step1Labels = raw41742step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41742step0 raw41742step0Labels permutation38 permutation2
    mixedMoment B raw41742step1 raw41742step1Labels = mixedMoment B raw41742step2 raw41742step2Labels := by
      have ha : raw41742step2 = raw41742step1 := by apply Matrix.ext; unfold raw41742step2 raw41742step1; decide +kernel
      have hl : raw41742step1Labels = labelEmbedding1 ∘ raw41742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41742step1 raw41742step1Labels raw41742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw41743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41743Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41743step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw41743step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41743step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41743step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41743 raw41743Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw41743 raw41743Labels = mixedMoment B raw41743step0 raw41743step0Labels := by
      have hz : ∀ j, raw41743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41743step0 = (fun i j => raw41743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41743step0 raw41743; decide +kernel
      have hl : raw41743step0Labels = raw41743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41743 raw41743Labels permutation434 hz
    mixedMoment B raw41743step0 raw41743step0Labels = mixedMoment B raw41743step1 raw41743step1Labels := by
      have ha : raw41743step1 = (fun i j => raw41743step0 (permutation47 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41743step1 raw41743step0; decide +kernel
      have hl : raw41743step1Labels = raw41743step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41743step0 raw41743step0Labels permutation47 permutation7
    mixedMoment B raw41743step1 raw41743step1Labels = mixedMoment B raw41743step2 raw41743step2Labels := by
      have ha : raw41743step2 = -raw41743step1 := by apply Matrix.ext; change ∀ i j, raw41743step2 i j = -(raw41743step1 i j); unfold raw41743step2 raw41743step1; decide +kernel
      have hl : raw41743step2Labels = raw41743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41743step2 raw41743step2Labels = mixedMoment B raw41743step3 raw41743step3Labels := by
      have ha : raw41743step3 = raw41743step2 := by apply Matrix.ext; unfold raw41743step3 raw41743step2; decide +kernel
      have hl : raw41743step2Labels = labelEmbedding6 ∘ raw41743step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41743step2 raw41743step2Labels raw41743step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw41744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41744Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41744 raw41744Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw41744 raw41744Labels = mixedMoment B raw41744step0 raw41744step0Labels := by
      have hz : ∀ j, raw41744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41744step0 = (fun i j => raw41744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41744step0 raw41744; decide +kernel
      have hl : raw41744step0Labels = raw41744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41744 raw41744Labels permutation434 hz
    mixedMoment B raw41744step0 raw41744step0Labels = mixedMoment B raw41744step1 raw41744step1Labels := by
      have ha : raw41744step1 = (fun i j => raw41744step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41744step1 raw41744step0; decide +kernel
      have hl : raw41744step1Labels = raw41744step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41744step0 raw41744step0Labels permutation38 permutation2
    mixedMoment B raw41744step1 raw41744step1Labels = mixedMoment B raw41744step2 raw41744step2Labels := by
      have ha : raw41744step2 = raw41744step1 := by apply Matrix.ext; unfold raw41744step2 raw41744step1; decide +kernel
      have hl : raw41744step1Labels = labelEmbedding1 ∘ raw41744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41744step1 raw41744step1Labels raw41744step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2249 node2249Labels := by rfl

def raw41745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41745Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41745step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw41745step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41745step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41745step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41745step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41745 raw41745Labels = mixedMoment B node4700 node4700Labels := by
  calc
    mixedMoment B raw41745 raw41745Labels = mixedMoment B raw41745step0 raw41745step0Labels := by
      have hz : ∀ j, raw41745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41745step0 = (fun i j => raw41745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41745step0 raw41745; decide +kernel
      have hl : raw41745step0Labels = raw41745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41745 raw41745Labels permutation434 hz
    mixedMoment B raw41745step0 raw41745step0Labels = mixedMoment B raw41745step1 raw41745step1Labels := by
      have ha : raw41745step1 = (fun i j => raw41745step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41745step1 raw41745step0; decide +kernel
      have hl : raw41745step1Labels = raw41745step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41745step0 raw41745step0Labels permutation46 permutation7
    mixedMoment B raw41745step1 raw41745step1Labels = mixedMoment B raw41745step2 raw41745step2Labels := by
      have ha : raw41745step2 = -raw41745step1 := by apply Matrix.ext; change ∀ i j, raw41745step2 i j = -(raw41745step1 i j); unfold raw41745step2 raw41745step1; decide +kernel
      have hl : raw41745step2Labels = raw41745step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41745step2 raw41745step2Labels = mixedMoment B raw41745step3 raw41745step3Labels := by
      have ha : raw41745step3 = raw41745step2 := by apply Matrix.ext; unfold raw41745step3 raw41745step2; decide +kernel
      have hl : raw41745step2Labels = labelEmbedding6 ∘ raw41745step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41745step2 raw41745step2Labels raw41745step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4700 node4700Labels := by rfl

def raw41746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41746Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41746 raw41746Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw41746 raw41746Labels = mixedMoment B raw41746step0 raw41746step0Labels := by
      have ha : raw41746step0 = (fun i j => raw41746 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41746step0 raw41746; decide +kernel
      have hl : raw41746step0Labels = raw41746Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41746 raw41746Labels permutation206 permutation2
    mixedMoment B raw41746step0 raw41746step0Labels = mixedMoment B raw41746step1 raw41746step1Labels := by
      have ha : raw41746step1 = raw41746step0 := by apply Matrix.ext; unfold raw41746step1 raw41746step0; decide +kernel
      have hl : raw41746step0Labels = labelEmbedding1 ∘ raw41746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41746step0 raw41746step0Labels raw41746step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw41747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41747Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw41747step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41747step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41747step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41747step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41747 raw41747Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw41747 raw41747Labels = mixedMoment B raw41747step0 raw41747step0Labels := by
      have ha : raw41747step0 = (fun i j => raw41747 (permutation221 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41747step0 raw41747; decide +kernel
      have hl : raw41747step0Labels = raw41747Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41747 raw41747Labels permutation221 permutation7
    mixedMoment B raw41747step0 raw41747step0Labels = mixedMoment B raw41747step1 raw41747step1Labels := by
      have ha : raw41747step1 = -raw41747step0 := by apply Matrix.ext; change ∀ i j, raw41747step1 i j = -(raw41747step0 i j); unfold raw41747step1 raw41747step0; decide +kernel
      have hl : raw41747step1Labels = raw41747step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41747step1 raw41747step1Labels = mixedMoment B raw41747step2 raw41747step2Labels := by
      have ha : raw41747step2 = raw41747step1 := by apply Matrix.ext; unfold raw41747step2 raw41747step1; decide +kernel
      have hl : raw41747step1Labels = labelEmbedding6 ∘ raw41747step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41747step1 raw41747step1Labels raw41747step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw41748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41748Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41748step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41748 raw41748Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw41748 raw41748Labels = mixedMoment B raw41748step0 raw41748step0Labels := by
      have ha : raw41748step0 = (fun i j => raw41748 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41748step0 raw41748; decide +kernel
      have hl : raw41748step0Labels = raw41748Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41748 raw41748Labels permutation206 permutation2
    mixedMoment B raw41748step0 raw41748step0Labels = mixedMoment B raw41748step1 raw41748step1Labels := by
      have ha : raw41748step1 = raw41748step0 := by apply Matrix.ext; unfold raw41748step1 raw41748step0; decide +kernel
      have hl : raw41748step0Labels = labelEmbedding1 ∘ raw41748step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41748step0 raw41748step0Labels raw41748step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw41749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41749Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw41749step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41749step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41749step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41749 raw41749Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw41749 raw41749Labels = mixedMoment B raw41749step0 raw41749step0Labels := by
      have ha : raw41749step0 = (fun i j => raw41749 (permutation215 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41749step0 raw41749; decide +kernel
      have hl : raw41749step0Labels = raw41749Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41749 raw41749Labels permutation215 permutation7
    mixedMoment B raw41749step0 raw41749step0Labels = mixedMoment B raw41749step1 raw41749step1Labels := by
      have ha : raw41749step1 = -raw41749step0 := by apply Matrix.ext; change ∀ i j, raw41749step1 i j = -(raw41749step0 i j); unfold raw41749step1 raw41749step0; decide +kernel
      have hl : raw41749step1Labels = raw41749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41749step1 raw41749step1Labels = mixedMoment B raw41749step2 raw41749step2Labels := by
      have ha : raw41749step2 = raw41749step1 := by apply Matrix.ext; unfold raw41749step2 raw41749step1; decide +kernel
      have hl : raw41749step1Labels = labelEmbedding6 ∘ raw41749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41749step1 raw41749step1Labels raw41749step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw41750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41750Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41750step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41750 raw41750Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw41750 raw41750Labels = mixedMoment B raw41750step0 raw41750step0Labels := by
      have ha : raw41750step0 = (fun i j => raw41750 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41750step0 raw41750; decide +kernel
      have hl : raw41750step0Labels = raw41750Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41750 raw41750Labels permutation206 permutation2
    mixedMoment B raw41750step0 raw41750step0Labels = mixedMoment B raw41750step1 raw41750step1Labels := by
      have ha : raw41750step1 = raw41750step0 := by apply Matrix.ext; unfold raw41750step1 raw41750step0; decide +kernel
      have hl : raw41750step0Labels = labelEmbedding1 ∘ raw41750step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41750step0 raw41750step0Labels raw41750step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

def raw41751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41751Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw41751step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41751step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41751step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41751 raw41751Labels = mixedMoment B node4773 node4773Labels := by
  calc
    mixedMoment B raw41751 raw41751Labels = mixedMoment B raw41751step0 raw41751step0Labels := by
      have ha : raw41751step0 = (fun i j => raw41751 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41751step0 raw41751; decide +kernel
      have hl : raw41751step0Labels = raw41751Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41751 raw41751Labels permutation214 permutation7
    mixedMoment B raw41751step0 raw41751step0Labels = mixedMoment B raw41751step1 raw41751step1Labels := by
      have ha : raw41751step1 = -raw41751step0 := by apply Matrix.ext; change ∀ i j, raw41751step1 i j = -(raw41751step0 i j); unfold raw41751step1 raw41751step0; decide +kernel
      have hl : raw41751step1Labels = raw41751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41751step1 raw41751step1Labels = mixedMoment B raw41751step2 raw41751step2Labels := by
      have ha : raw41751step2 = raw41751step1 := by apply Matrix.ext; unfold raw41751step2 raw41751step1; decide +kernel
      have hl : raw41751step1Labels = labelEmbedding6 ∘ raw41751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41751step1 raw41751step1Labels raw41751step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4773 node4773Labels := by rfl

def raw41752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41752Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41752step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41752 raw41752Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw41752 raw41752Labels = mixedMoment B raw41752step0 raw41752step0Labels := by
      have ha : raw41752step0 = (fun i j => raw41752 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41752step0 raw41752; decide +kernel
      have hl : raw41752step0Labels = raw41752Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41752 raw41752Labels permutation206 permutation2
    mixedMoment B raw41752step0 raw41752step0Labels = mixedMoment B raw41752step1 raw41752step1Labels := by
      have ha : raw41752step1 = raw41752step0 := by apply Matrix.ext; unfold raw41752step1 raw41752step0; decide +kernel
      have hl : raw41752step0Labels = labelEmbedding1 ∘ raw41752step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41752step0 raw41752step0Labels raw41752step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2144 node2144Labels := by rfl

def raw41753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41753Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw41753step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41753step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41753step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41753 raw41753Labels = mixedMoment B node4665 node4665Labels := by
  calc
    mixedMoment B raw41753 raw41753Labels = mixedMoment B raw41753step0 raw41753step0Labels := by
      have ha : raw41753step0 = (fun i j => raw41753 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41753step0 raw41753; decide +kernel
      have hl : raw41753step0Labels = raw41753Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41753 raw41753Labels permutation214 permutation7
    mixedMoment B raw41753step0 raw41753step0Labels = mixedMoment B raw41753step1 raw41753step1Labels := by
      have ha : raw41753step1 = -raw41753step0 := by apply Matrix.ext; change ∀ i j, raw41753step1 i j = -(raw41753step0 i j); unfold raw41753step1 raw41753step0; decide +kernel
      have hl : raw41753step1Labels = raw41753step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41753step1 raw41753step1Labels = mixedMoment B raw41753step2 raw41753step2Labels := by
      have ha : raw41753step2 = raw41753step1 := by apply Matrix.ext; unfold raw41753step2 raw41753step1; decide +kernel
      have hl : raw41753step1Labels = labelEmbedding6 ∘ raw41753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41753step1 raw41753step1Labels raw41753step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4665 node4665Labels := by rfl

def raw41754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41754Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41754step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41754 raw41754Labels = mixedMoment B node2248 node2248Labels := by
  calc
    mixedMoment B raw41754 raw41754Labels = mixedMoment B raw41754step0 raw41754step0Labels := by
      have ha : raw41754step0 = (fun i j => raw41754 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41754step0 raw41754; decide +kernel
      have hl : raw41754step0Labels = raw41754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41754 raw41754Labels permutation180 permutation2
    mixedMoment B raw41754step0 raw41754step0Labels = mixedMoment B raw41754step1 raw41754step1Labels := by
      have ha : raw41754step1 = raw41754step0 := by apply Matrix.ext; unfold raw41754step1 raw41754step0; decide +kernel
      have hl : raw41754step0Labels = labelEmbedding1 ∘ raw41754step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41754step0 raw41754step0Labels raw41754step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2248 node2248Labels := by rfl

def raw41755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41755Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41755step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41755step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41755step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41755step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41755 raw41755Labels = mixedMoment B node4698 node4698Labels := by
  calc
    mixedMoment B raw41755 raw41755Labels = mixedMoment B raw41755step0 raw41755step0Labels := by
      have ha : raw41755step0 = (fun i j => raw41755 (permutation255 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41755step0 raw41755; decide +kernel
      have hl : raw41755step0Labels = raw41755Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41755 raw41755Labels permutation255 permutation7
    mixedMoment B raw41755step0 raw41755step0Labels = mixedMoment B raw41755step1 raw41755step1Labels := by
      have ha : raw41755step1 = -raw41755step0 := by apply Matrix.ext; change ∀ i j, raw41755step1 i j = -(raw41755step0 i j); unfold raw41755step1 raw41755step0; decide +kernel
      have hl : raw41755step1Labels = raw41755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41755step1 raw41755step1Labels = mixedMoment B raw41755step2 raw41755step2Labels := by
      have ha : raw41755step2 = raw41755step1 := by apply Matrix.ext; unfold raw41755step2 raw41755step1; decide +kernel
      have hl : raw41755step1Labels = labelEmbedding6 ∘ raw41755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41755step1 raw41755step1Labels raw41755step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4698 node4698Labels := by rfl

def raw41756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41756Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41756step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41756 raw41756Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw41756 raw41756Labels = mixedMoment B raw41756step0 raw41756step0Labels := by
      have ha : raw41756step0 = (fun i j => raw41756 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41756step0 raw41756; decide +kernel
      have hl : raw41756step0Labels = raw41756Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41756 raw41756Labels permutation181 permutation2
    mixedMoment B raw41756step0 raw41756step0Labels = mixedMoment B raw41756step1 raw41756step1Labels := by
      have ha : raw41756step1 = raw41756step0 := by apply Matrix.ext; unfold raw41756step1 raw41756step0; decide +kernel
      have hl : raw41756step0Labels = labelEmbedding1 ∘ raw41756step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41756step0 raw41756step0Labels raw41756step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw41757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41757Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw41757step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41757step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41757step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41757step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41757 raw41757Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw41757 raw41757Labels = mixedMoment B raw41757step0 raw41757step0Labels := by
      have ha : raw41757step0 = (fun i j => raw41757 (permutation263 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41757step0 raw41757; decide +kernel
      have hl : raw41757step0Labels = raw41757Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41757 raw41757Labels permutation263 permutation7
    mixedMoment B raw41757step0 raw41757step0Labels = mixedMoment B raw41757step1 raw41757step1Labels := by
      have ha : raw41757step1 = -raw41757step0 := by apply Matrix.ext; change ∀ i j, raw41757step1 i j = -(raw41757step0 i j); unfold raw41757step1 raw41757step0; decide +kernel
      have hl : raw41757step1Labels = raw41757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41757step1 raw41757step1Labels = mixedMoment B raw41757step2 raw41757step2Labels := by
      have ha : raw41757step2 = raw41757step1 := by apply Matrix.ext; unfold raw41757step2 raw41757step1; decide +kernel
      have hl : raw41757step1Labels = labelEmbedding6 ∘ raw41757step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41757step1 raw41757step1Labels raw41757step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw41758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41758Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41758step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41758 raw41758Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw41758 raw41758Labels = mixedMoment B raw41758step0 raw41758step0Labels := by
      have ha : raw41758step0 = (fun i j => raw41758 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41758step0 raw41758; decide +kernel
      have hl : raw41758step0Labels = raw41758Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41758 raw41758Labels permutation176 permutation2
    mixedMoment B raw41758step0 raw41758step0Labels = mixedMoment B raw41758step1 raw41758step1Labels := by
      have ha : raw41758step1 = raw41758step0 := by apply Matrix.ext; unfold raw41758step1 raw41758step0; decide +kernel
      have hl : raw41758step0Labels = labelEmbedding1 ∘ raw41758step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41758step0 raw41758step0Labels raw41758step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2252 node2252Labels := by rfl

def raw41759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41759Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw41759step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41759step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41759step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41759step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41759 raw41759Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw41759 raw41759Labels = mixedMoment B raw41759step0 raw41759step0Labels := by
      have ha : raw41759step0 = (fun i j => raw41759 (permutation217 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41759step0 raw41759; decide +kernel
      have hl : raw41759step0Labels = raw41759Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41759 raw41759Labels permutation217 permutation7
    mixedMoment B raw41759step0 raw41759step0Labels = mixedMoment B raw41759step1 raw41759step1Labels := by
      have ha : raw41759step1 = -raw41759step0 := by apply Matrix.ext; change ∀ i j, raw41759step1 i j = -(raw41759step0 i j); unfold raw41759step1 raw41759step0; decide +kernel
      have hl : raw41759step1Labels = raw41759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41759step1 raw41759step1Labels = mixedMoment B raw41759step2 raw41759step2Labels := by
      have ha : raw41759step2 = raw41759step1 := by apply Matrix.ext; unfold raw41759step2 raw41759step1; decide +kernel
      have hl : raw41759step1Labels = labelEmbedding6 ∘ raw41759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41759step1 raw41759step1Labels raw41759step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw41760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41760Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41760step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw41760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw41760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41760 raw41760Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw41760 raw41760Labels = mixedMoment B raw41760step0 raw41760step0Labels := by
      have hz : ∀ j, raw41760 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41760step0 = (fun i j => raw41760 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41760step0 raw41760; decide +kernel
      have hl : raw41760step0Labels = raw41760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41760 raw41760Labels permutation434 hz
    mixedMoment B raw41760step0 raw41760step0Labels = mixedMoment B raw41760step1 raw41760step1Labels := by
      have hz : ∀ j, raw41760step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41760step1 = (fun i j => raw41760step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41760step1 raw41760step0; decide +kernel
      have hl : raw41760step1Labels = raw41760step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41760step0 raw41760step0Labels permutation80 hz
    mixedMoment B raw41760step1 raw41760step1Labels = mixedMoment B raw41760step2 raw41760step2Labels := by
      have ha : raw41760step2 = raw41760step1 := by apply Matrix.ext; unfold raw41760step2 raw41760step1; decide +kernel
      have hl : raw41760step1Labels = labelEmbedding1 ∘ raw41760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41760step1 raw41760step1Labels raw41760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw41761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41761Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41761step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw41761step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw41761step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw41761step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41761step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw41761step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41761 raw41761Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw41761 raw41761Labels = mixedMoment B raw41761step0 raw41761step0Labels := by
      have hz : ∀ j, raw41761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41761step0 = (fun i j => raw41761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41761step0 raw41761; decide +kernel
      have hl : raw41761step0Labels = raw41761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41761 raw41761Labels permutation434 hz
    mixedMoment B raw41761step0 raw41761step0Labels = mixedMoment B raw41761step1 raw41761step1Labels := by
      have hz : ∀ j, raw41761step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41761step1 = (fun i j => raw41761step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41761step1 raw41761step0; decide +kernel
      have hl : raw41761step1Labels = raw41761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41761step0 raw41761step0Labels permutation80 hz
    mixedMoment B raw41761step1 raw41761step1Labels = mixedMoment B raw41761step2 raw41761step2Labels := by
      have ha : raw41761step2 = (fun i j => raw41761step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41761step2 raw41761step1; decide +kernel
      have hl : raw41761step2Labels = raw41761step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41761step1 raw41761step1Labels permutation12 permutation7
    mixedMoment B raw41761step2 raw41761step2Labels = mixedMoment B raw41761step3 raw41761step3Labels := by
      have ha : raw41761step3 = -raw41761step2 := by apply Matrix.ext; change ∀ i j, raw41761step3 i j = -(raw41761step2 i j); unfold raw41761step3 raw41761step2; decide +kernel
      have hl : raw41761step3Labels = raw41761step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41761step3 raw41761step3Labels = mixedMoment B raw41761step4 raw41761step4Labels := by
      have ha : raw41761step4 = raw41761step3 := by apply Matrix.ext; unfold raw41761step4 raw41761step3; decide +kernel
      have hl : raw41761step3Labels = labelEmbedding6 ∘ raw41761step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41761step3 raw41761step3Labels raw41761step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4884 node4884Labels := by rfl

def raw41762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41762Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41762step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw41762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw41762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41762 raw41762Labels = mixedMoment B node2273 node2273Labels := by
  calc
    mixedMoment B raw41762 raw41762Labels = mixedMoment B raw41762step0 raw41762step0Labels := by
      have hz : ∀ j, raw41762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41762step0 = (fun i j => raw41762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41762step0 raw41762; decide +kernel
      have hl : raw41762step0Labels = raw41762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41762 raw41762Labels permutation434 hz
    mixedMoment B raw41762step0 raw41762step0Labels = mixedMoment B raw41762step1 raw41762step1Labels := by
      have hz : ∀ j, raw41762step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41762step1 = (fun i j => raw41762step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41762step1 raw41762step0; decide +kernel
      have hl : raw41762step1Labels = raw41762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41762step0 raw41762step0Labels permutation80 hz
    mixedMoment B raw41762step1 raw41762step1Labels = mixedMoment B raw41762step2 raw41762step2Labels := by
      have ha : raw41762step2 = raw41762step1 := by apply Matrix.ext; unfold raw41762step2 raw41762step1; decide +kernel
      have hl : raw41762step1Labels = labelEmbedding1 ∘ raw41762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41762step1 raw41762step1Labels raw41762step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2273 node2273Labels := by rfl

def raw41763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41763Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41763step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw41763step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41763step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41763step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41763step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41763step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41763 raw41763Labels = mixedMoment B node4704 node4704Labels := by
  calc
    mixedMoment B raw41763 raw41763Labels = mixedMoment B raw41763step0 raw41763step0Labels := by
      have hz : ∀ j, raw41763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41763step0 = (fun i j => raw41763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41763step0 raw41763; decide +kernel
      have hl : raw41763step0Labels = raw41763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41763 raw41763Labels permutation434 hz
    mixedMoment B raw41763step0 raw41763step0Labels = mixedMoment B raw41763step1 raw41763step1Labels := by
      have hz : ∀ j, raw41763step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41763step1 = (fun i j => raw41763step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41763step1 raw41763step0; decide +kernel
      have hl : raw41763step1Labels = raw41763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41763step0 raw41763step0Labels permutation80 hz
    mixedMoment B raw41763step1 raw41763step1Labels = mixedMoment B raw41763step2 raw41763step2Labels := by
      have ha : raw41763step2 = (fun i j => raw41763step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41763step2 raw41763step1; decide +kernel
      have hl : raw41763step2Labels = raw41763step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41763step1 raw41763step1Labels permutation10 permutation7
    mixedMoment B raw41763step2 raw41763step2Labels = mixedMoment B raw41763step3 raw41763step3Labels := by
      have ha : raw41763step3 = -raw41763step2 := by apply Matrix.ext; change ∀ i j, raw41763step3 i j = -(raw41763step2 i j); unfold raw41763step3 raw41763step2; decide +kernel
      have hl : raw41763step3Labels = raw41763step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41763step3 raw41763step3Labels = mixedMoment B raw41763step4 raw41763step4Labels := by
      have ha : raw41763step4 = raw41763step3 := by apply Matrix.ext; unfold raw41763step4 raw41763step3; decide +kernel
      have hl : raw41763step3Labels = labelEmbedding6 ∘ raw41763step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41763step3 raw41763step3Labels raw41763step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4704 node4704Labels := by rfl

def raw41764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41764Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41764step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw41764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw41764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41764 raw41764Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw41764 raw41764Labels = mixedMoment B raw41764step0 raw41764step0Labels := by
      have hz : ∀ j, raw41764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41764step0 = (fun i j => raw41764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41764step0 raw41764; decide +kernel
      have hl : raw41764step0Labels = raw41764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41764 raw41764Labels permutation346 hz
    mixedMoment B raw41764step0 raw41764step0Labels = mixedMoment B raw41764step1 raw41764step1Labels := by
      have ha : raw41764step1 = (fun i j => raw41764step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41764step1 raw41764step0; decide +kernel
      have hl : raw41764step1Labels = raw41764step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41764step0 raw41764step0Labels permutation38 permutation2
    mixedMoment B raw41764step1 raw41764step1Labels = mixedMoment B raw41764step2 raw41764step2Labels := by
      have ha : raw41764step2 = raw41764step1 := by apply Matrix.ext; unfold raw41764step2 raw41764step1; decide +kernel
      have hl : raw41764step1Labels = labelEmbedding1 ∘ raw41764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41764step1 raw41764step1Labels raw41764step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw41765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41765Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41765step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw41765step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw41765step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41765step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw41765step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41765 raw41765Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw41765 raw41765Labels = mixedMoment B raw41765step0 raw41765step0Labels := by
      have hz : ∀ j, raw41765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41765step0 = (fun i j => raw41765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41765step0 raw41765; decide +kernel
      have hl : raw41765step0Labels = raw41765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41765 raw41765Labels permutation346 hz
    mixedMoment B raw41765step0 raw41765step0Labels = mixedMoment B raw41765step1 raw41765step1Labels := by
      have ha : raw41765step1 = (fun i j => raw41765step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41765step1 raw41765step0; decide +kernel
      have hl : raw41765step1Labels = raw41765step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41765step0 raw41765step0Labels permutation42 permutation7
    mixedMoment B raw41765step1 raw41765step1Labels = mixedMoment B raw41765step2 raw41765step2Labels := by
      have ha : raw41765step2 = -raw41765step1 := by apply Matrix.ext; change ∀ i j, raw41765step2 i j = -(raw41765step1 i j); unfold raw41765step2 raw41765step1; decide +kernel
      have hl : raw41765step2Labels = raw41765step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41765step2 raw41765step2Labels = mixedMoment B raw41765step3 raw41765step3Labels := by
      have ha : raw41765step3 = raw41765step2 := by apply Matrix.ext; unfold raw41765step3 raw41765step2; decide +kernel
      have hl : raw41765step2Labels = labelEmbedding6 ∘ raw41765step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41765step2 raw41765step2Labels raw41765step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw41766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41766Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41766step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw41766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw41766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41766 raw41766Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw41766 raw41766Labels = mixedMoment B raw41766step0 raw41766step0Labels := by
      have hz : ∀ j, raw41766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41766step0 = (fun i j => raw41766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41766step0 raw41766; decide +kernel
      have hl : raw41766step0Labels = raw41766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41766 raw41766Labels permutation346 hz
    mixedMoment B raw41766step0 raw41766step0Labels = mixedMoment B raw41766step1 raw41766step1Labels := by
      have ha : raw41766step1 = (fun i j => raw41766step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41766step1 raw41766step0; decide +kernel
      have hl : raw41766step1Labels = raw41766step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41766step0 raw41766step0Labels permutation38 permutation2
    mixedMoment B raw41766step1 raw41766step1Labels = mixedMoment B raw41766step2 raw41766step2Labels := by
      have ha : raw41766step2 = raw41766step1 := by apply Matrix.ext; unfold raw41766step2 raw41766step1; decide +kernel
      have hl : raw41766step1Labels = labelEmbedding1 ∘ raw41766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41766step1 raw41766step1Labels raw41766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

def raw41767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41767Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41767step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41767step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41767 raw41767Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw41767 raw41767Labels = mixedMoment B raw41767step0 raw41767step0Labels := by
      have hz : ∀ j, raw41767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41767step0 = (fun i j => raw41767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41767step0 raw41767; decide +kernel
      have hl : raw41767step0Labels = raw41767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41767 raw41767Labels permutation346 hz
    mixedMoment B raw41767step0 raw41767step0Labels = mixedMoment B raw41767step1 raw41767step1Labels := by
      have ha : raw41767step1 = (fun i j => raw41767step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41767step1 raw41767step0; decide +kernel
      have hl : raw41767step1Labels = raw41767step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41767step0 raw41767step0Labels permutation40 permutation7
    mixedMoment B raw41767step1 raw41767step1Labels = mixedMoment B raw41767step2 raw41767step2Labels := by
      have ha : raw41767step2 = -raw41767step1 := by apply Matrix.ext; change ∀ i j, raw41767step2 i j = -(raw41767step1 i j); unfold raw41767step2 raw41767step1; decide +kernel
      have hl : raw41767step2Labels = raw41767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41767step2 raw41767step2Labels = mixedMoment B raw41767step3 raw41767step3Labels := by
      have ha : raw41767step3 = raw41767step2 := by apply Matrix.ext; unfold raw41767step3 raw41767step2; decide +kernel
      have hl : raw41767step2Labels = labelEmbedding6 ∘ raw41767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41767step2 raw41767step2Labels raw41767step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4776 node4776Labels := by rfl

def raw41768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41768Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41768step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41768 raw41768Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw41768 raw41768Labels = mixedMoment B raw41768step0 raw41768step0Labels := by
      have hz : ∀ j, raw41768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41768step0 = (fun i j => raw41768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41768step0 raw41768; decide +kernel
      have hl : raw41768step0Labels = raw41768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41768 raw41768Labels permutation346 hz
    mixedMoment B raw41768step0 raw41768step0Labels = mixedMoment B raw41768step1 raw41768step1Labels := by
      have ha : raw41768step1 = (fun i j => raw41768step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41768step1 raw41768step0; decide +kernel
      have hl : raw41768step1Labels = raw41768step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41768step0 raw41768step0Labels permutation38 permutation2
    mixedMoment B raw41768step1 raw41768step1Labels = mixedMoment B raw41768step2 raw41768step2Labels := by
      have ha : raw41768step2 = raw41768step1 := by apply Matrix.ext; unfold raw41768step2 raw41768step1; decide +kernel
      have hl : raw41768step1Labels = labelEmbedding1 ∘ raw41768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41768step1 raw41768step1Labels raw41768step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2155 node2155Labels := by rfl

def raw41769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41769Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41769step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41769step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41769step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41769step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41769step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41769 raw41769Labels = mixedMoment B node4669 node4669Labels := by
  calc
    mixedMoment B raw41769 raw41769Labels = mixedMoment B raw41769step0 raw41769step0Labels := by
      have hz : ∀ j, raw41769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41769step0 = (fun i j => raw41769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41769step0 raw41769; decide +kernel
      have hl : raw41769step0Labels = raw41769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41769 raw41769Labels permutation346 hz
    mixedMoment B raw41769step0 raw41769step0Labels = mixedMoment B raw41769step1 raw41769step1Labels := by
      have ha : raw41769step1 = (fun i j => raw41769step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41769step1 raw41769step0; decide +kernel
      have hl : raw41769step1Labels = raw41769step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41769step0 raw41769step0Labels permutation40 permutation7
    mixedMoment B raw41769step1 raw41769step1Labels = mixedMoment B raw41769step2 raw41769step2Labels := by
      have ha : raw41769step2 = -raw41769step1 := by apply Matrix.ext; change ∀ i j, raw41769step2 i j = -(raw41769step1 i j); unfold raw41769step2 raw41769step1; decide +kernel
      have hl : raw41769step2Labels = raw41769step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41769step2 raw41769step2Labels = mixedMoment B raw41769step3 raw41769step3Labels := by
      have ha : raw41769step3 = raw41769step2 := by apply Matrix.ext; unfold raw41769step3 raw41769step2; decide +kernel
      have hl : raw41769step2Labels = labelEmbedding6 ∘ raw41769step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41769step2 raw41769step2Labels raw41769step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4669 node4669Labels := by rfl

def raw41770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41770Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41770step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41770 raw41770Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw41770 raw41770Labels = mixedMoment B raw41770step0 raw41770step0Labels := by
      have hz : ∀ j, raw41770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41770step0 = (fun i j => raw41770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41770step0 raw41770; decide +kernel
      have hl : raw41770step0Labels = raw41770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41770 raw41770Labels permutation346 hz
    mixedMoment B raw41770step0 raw41770step0Labels = mixedMoment B raw41770step1 raw41770step1Labels := by
      have ha : raw41770step1 = (fun i j => raw41770step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41770step1 raw41770step0; decide +kernel
      have hl : raw41770step1Labels = raw41770step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41770step0 raw41770step0Labels permutation37 permutation2
    mixedMoment B raw41770step1 raw41770step1Labels = mixedMoment B raw41770step2 raw41770step2Labels := by
      have ha : raw41770step2 = raw41770step1 := by apply Matrix.ext; unfold raw41770step2 raw41770step1; decide +kernel
      have hl : raw41770step1Labels = labelEmbedding1 ∘ raw41770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41770step1 raw41770step1Labels raw41770step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

def raw41771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41771Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41771step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41771step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41771step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41771step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41771step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41771 raw41771Labels = mixedMoment B node4703 node4703Labels := by
  calc
    mixedMoment B raw41771 raw41771Labels = mixedMoment B raw41771step0 raw41771step0Labels := by
      have hz : ∀ j, raw41771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41771step0 = (fun i j => raw41771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41771step0 raw41771; decide +kernel
      have hl : raw41771step0Labels = raw41771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41771 raw41771Labels permutation346 hz
    mixedMoment B raw41771step0 raw41771step0Labels = mixedMoment B raw41771step1 raw41771step1Labels := by
      have ha : raw41771step1 = (fun i j => raw41771step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41771step1 raw41771step0; decide +kernel
      have hl : raw41771step1Labels = raw41771step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41771step0 raw41771step0Labels permutation54 permutation7
    mixedMoment B raw41771step1 raw41771step1Labels = mixedMoment B raw41771step2 raw41771step2Labels := by
      have ha : raw41771step2 = -raw41771step1 := by apply Matrix.ext; change ∀ i j, raw41771step2 i j = -(raw41771step1 i j); unfold raw41771step2 raw41771step1; decide +kernel
      have hl : raw41771step2Labels = raw41771step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41771step2 raw41771step2Labels = mixedMoment B raw41771step3 raw41771step3Labels := by
      have ha : raw41771step3 = raw41771step2 := by apply Matrix.ext; unfold raw41771step3 raw41771step2; decide +kernel
      have hl : raw41771step2Labels = labelEmbedding6 ∘ raw41771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41771step2 raw41771step2Labels raw41771step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4703 node4703Labels := by rfl

def raw41772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41772Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41772step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41772 raw41772Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw41772 raw41772Labels = mixedMoment B raw41772step0 raw41772step0Labels := by
      have hz : ∀ j, raw41772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41772step0 = (fun i j => raw41772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41772step0 raw41772; decide +kernel
      have hl : raw41772step0Labels = raw41772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41772 raw41772Labels permutation346 hz
    mixedMoment B raw41772step0 raw41772step0Labels = mixedMoment B raw41772step1 raw41772step1Labels := by
      have ha : raw41772step1 = (fun i j => raw41772step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41772step1 raw41772step0; decide +kernel
      have hl : raw41772step1Labels = raw41772step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41772step0 raw41772step0Labels permutation37 permutation2
    mixedMoment B raw41772step1 raw41772step1Labels = mixedMoment B raw41772step2 raw41772step2Labels := by
      have ha : raw41772step2 = raw41772step1 := by apply Matrix.ext; unfold raw41772step2 raw41772step1; decide +kernel
      have hl : raw41772step1Labels = labelEmbedding1 ∘ raw41772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41772step1 raw41772step1Labels raw41772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw41773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41773Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41773step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41773step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41773step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41773step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41773step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41773 raw41773Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw41773 raw41773Labels = mixedMoment B raw41773step0 raw41773step0Labels := by
      have hz : ∀ j, raw41773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41773step0 = (fun i j => raw41773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41773step0 raw41773; decide +kernel
      have hl : raw41773step0Labels = raw41773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41773 raw41773Labels permutation346 hz
    mixedMoment B raw41773step0 raw41773step0Labels = mixedMoment B raw41773step1 raw41773step1Labels := by
      have ha : raw41773step1 = (fun i j => raw41773step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41773step1 raw41773step0; decide +kernel
      have hl : raw41773step1Labels = raw41773step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41773step0 raw41773step0Labels permutation54 permutation7
    mixedMoment B raw41773step1 raw41773step1Labels = mixedMoment B raw41773step2 raw41773step2Labels := by
      have ha : raw41773step2 = -raw41773step1 := by apply Matrix.ext; change ∀ i j, raw41773step2 i j = -(raw41773step1 i j); unfold raw41773step2 raw41773step1; decide +kernel
      have hl : raw41773step2Labels = raw41773step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41773step2 raw41773step2Labels = mixedMoment B raw41773step3 raw41773step3Labels := by
      have ha : raw41773step3 = raw41773step2 := by apply Matrix.ext; unfold raw41773step3 raw41773step2; decide +kernel
      have hl : raw41773step2Labels = labelEmbedding6 ∘ raw41773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41773step2 raw41773step2Labels raw41773step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw41774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41774Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41774step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41774 raw41774Labels = mixedMoment B node2176 node2176Labels := by
  calc
    mixedMoment B raw41774 raw41774Labels = mixedMoment B raw41774step0 raw41774step0Labels := by
      have ha : raw41774step0 = (fun i j => raw41774 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41774step0 raw41774; decide +kernel
      have hl : raw41774step0Labels = raw41774Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41774 raw41774Labels permutation182 permutation2
    mixedMoment B raw41774step0 raw41774step0Labels = mixedMoment B raw41774step1 raw41774step1Labels := by
      have ha : raw41774step1 = raw41774step0 := by apply Matrix.ext; unfold raw41774step1 raw41774step0; decide +kernel
      have hl : raw41774step0Labels = labelEmbedding1 ∘ raw41774step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41774step0 raw41774step0Labels raw41774step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2176 node2176Labels := by rfl

def raw41775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41775Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41775step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41775step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41775step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41775 raw41775Labels = mixedMoment B node4756 node4756Labels := by
  calc
    mixedMoment B raw41775 raw41775Labels = mixedMoment B raw41775step0 raw41775step0Labels := by
      have ha : raw41775step0 = (fun i j => raw41775 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41775step0 raw41775; decide +kernel
      have hl : raw41775step0Labels = raw41775Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41775 raw41775Labels permutation184 permutation7
    mixedMoment B raw41775step0 raw41775step0Labels = mixedMoment B raw41775step1 raw41775step1Labels := by
      have ha : raw41775step1 = -raw41775step0 := by apply Matrix.ext; change ∀ i j, raw41775step1 i j = -(raw41775step0 i j); unfold raw41775step1 raw41775step0; decide +kernel
      have hl : raw41775step1Labels = raw41775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41775step1 raw41775step1Labels = mixedMoment B raw41775step2 raw41775step2Labels := by
      have ha : raw41775step2 = raw41775step1 := by apply Matrix.ext; unfold raw41775step2 raw41775step1; decide +kernel
      have hl : raw41775step1Labels = labelEmbedding6 ∘ raw41775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41775step1 raw41775step1Labels raw41775step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4756 node4756Labels := by rfl

def raw41776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41776Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41776step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41776 raw41776Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw41776 raw41776Labels = mixedMoment B raw41776step0 raw41776step0Labels := by
      have ha : raw41776step0 = (fun i j => raw41776 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41776step0 raw41776; decide +kernel
      have hl : raw41776step0Labels = raw41776Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41776 raw41776Labels permutation181 permutation2
    mixedMoment B raw41776step0 raw41776step0Labels = mixedMoment B raw41776step1 raw41776step1Labels := by
      have ha : raw41776step1 = raw41776step0 := by apply Matrix.ext; unfold raw41776step1 raw41776step0; decide +kernel
      have hl : raw41776step0Labels = labelEmbedding1 ∘ raw41776step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41776step0 raw41776step0Labels raw41776step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

def raw41777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41777Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41777step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41777step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41777step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41777step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41777 raw41777Labels = mixedMoment B node4775 node4775Labels := by
  calc
    mixedMoment B raw41777 raw41777Labels = mixedMoment B raw41777step0 raw41777step0Labels := by
      have ha : raw41777step0 = (fun i j => raw41777 (permutation198 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41777step0 raw41777; decide +kernel
      have hl : raw41777step0Labels = raw41777Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41777 raw41777Labels permutation198 permutation7
    mixedMoment B raw41777step0 raw41777step0Labels = mixedMoment B raw41777step1 raw41777step1Labels := by
      have ha : raw41777step1 = -raw41777step0 := by apply Matrix.ext; change ∀ i j, raw41777step1 i j = -(raw41777step0 i j); unfold raw41777step1 raw41777step0; decide +kernel
      have hl : raw41777step1Labels = raw41777step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41777step1 raw41777step1Labels = mixedMoment B raw41777step2 raw41777step2Labels := by
      have ha : raw41777step2 = raw41777step1 := by apply Matrix.ext; unfold raw41777step2 raw41777step1; decide +kernel
      have hl : raw41777step1Labels = labelEmbedding6 ∘ raw41777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41777step1 raw41777step1Labels raw41777step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4775 node4775Labels := by rfl

def raw41778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41778Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41778step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41778 raw41778Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw41778 raw41778Labels = mixedMoment B raw41778step0 raw41778step0Labels := by
      have ha : raw41778step0 = (fun i j => raw41778 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41778step0 raw41778; decide +kernel
      have hl : raw41778step0Labels = raw41778Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41778 raw41778Labels permutation179 permutation2
    mixedMoment B raw41778step0 raw41778step0Labels = mixedMoment B raw41778step1 raw41778step1Labels := by
      have ha : raw41778step1 = raw41778step0 := by apply Matrix.ext; unfold raw41778step1 raw41778step0; decide +kernel
      have hl : raw41778step0Labels = labelEmbedding1 ∘ raw41778step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41778step0 raw41778step0Labels raw41778step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw41779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41779Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41779step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41779step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41779 raw41779Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw41779 raw41779Labels = mixedMoment B raw41779step0 raw41779step0Labels := by
      have ha : raw41779step0 = (fun i j => raw41779 (permutation192 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41779step0 raw41779; decide +kernel
      have hl : raw41779step0Labels = raw41779Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41779 raw41779Labels permutation192 permutation7
    mixedMoment B raw41779step0 raw41779step0Labels = mixedMoment B raw41779step1 raw41779step1Labels := by
      have ha : raw41779step1 = -raw41779step0 := by apply Matrix.ext; change ∀ i j, raw41779step1 i j = -(raw41779step0 i j); unfold raw41779step1 raw41779step0; decide +kernel
      have hl : raw41779step1Labels = raw41779step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41779step1 raw41779step1Labels = mixedMoment B raw41779step2 raw41779step2Labels := by
      have ha : raw41779step2 = raw41779step1 := by apply Matrix.ext; unfold raw41779step2 raw41779step1; decide +kernel
      have hl : raw41779step1Labels = labelEmbedding6 ∘ raw41779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41779step1 raw41779step1Labels raw41779step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw41780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41780Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41780step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41780 raw41780Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw41780 raw41780Labels = mixedMoment B raw41780step0 raw41780step0Labels := by
      have ha : raw41780step0 = (fun i j => raw41780 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41780step0 raw41780; decide +kernel
      have hl : raw41780step0Labels = raw41780Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41780 raw41780Labels permutation181 permutation2
    mixedMoment B raw41780step0 raw41780step0Labels = mixedMoment B raw41780step1 raw41780step1Labels := by
      have ha : raw41780step1 = raw41780step0 := by apply Matrix.ext; unfold raw41780step1 raw41780step0; decide +kernel
      have hl : raw41780step0Labels = labelEmbedding1 ∘ raw41780step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41780step0 raw41780step0Labels raw41780step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

def raw41781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41781Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41781step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41781step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41781step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41781step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41781 raw41781Labels = mixedMoment B node4668 node4668Labels := by
  calc
    mixedMoment B raw41781 raw41781Labels = mixedMoment B raw41781step0 raw41781step0Labels := by
      have ha : raw41781step0 = (fun i j => raw41781 (permutation198 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41781step0 raw41781; decide +kernel
      have hl : raw41781step0Labels = raw41781Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41781 raw41781Labels permutation198 permutation7
    mixedMoment B raw41781step0 raw41781step0Labels = mixedMoment B raw41781step1 raw41781step1Labels := by
      have ha : raw41781step1 = -raw41781step0 := by apply Matrix.ext; change ∀ i j, raw41781step1 i j = -(raw41781step0 i j); unfold raw41781step1 raw41781step0; decide +kernel
      have hl : raw41781step1Labels = raw41781step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41781step1 raw41781step1Labels = mixedMoment B raw41781step2 raw41781step2Labels := by
      have ha : raw41781step2 = raw41781step1 := by apply Matrix.ext; unfold raw41781step2 raw41781step1; decide +kernel
      have hl : raw41781step1Labels = labelEmbedding6 ∘ raw41781step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41781step1 raw41781step1Labels raw41781step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4668 node4668Labels := by rfl

def raw41782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41782Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41782step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41782 raw41782Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw41782 raw41782Labels = mixedMoment B raw41782step0 raw41782step0Labels := by
      have hz : ∀ j, raw41782 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41782step0 = (fun i j => raw41782 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41782step0 raw41782; decide +kernel
      have hl : raw41782step0Labels = raw41782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41782 raw41782Labels permutation520 hz
    mixedMoment B raw41782step0 raw41782step0Labels = mixedMoment B raw41782step1 raw41782step1Labels := by
      have ha : raw41782step1 = raw41782step0 := by apply Matrix.ext; unfold raw41782step1 raw41782step0; decide +kernel
      have hl : raw41782step0Labels = labelEmbedding1 ∘ raw41782step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41782step0 raw41782step0Labels raw41782step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2235 node2235Labels := by rfl

def raw41783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41783Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41783step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41783 raw41783Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw41783 raw41783Labels = mixedMoment B raw41783step0 raw41783step0Labels := by
      have hz : ∀ j, raw41783 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41783step0 = (fun i j => raw41783 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41783step0 raw41783; decide +kernel
      have hl : raw41783step0Labels = raw41783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41783 raw41783Labels permutation520 hz
    mixedMoment B raw41783step0 raw41783step0Labels = mixedMoment B raw41783step1 raw41783step1Labels := by
      have ha : raw41783step1 = raw41783step0 := by apply Matrix.ext; unfold raw41783step1 raw41783step0; decide +kernel
      have hl : raw41783step0Labels = labelEmbedding8 ∘ raw41783step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41783step0 raw41783step0Labels raw41783step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4886 node4886Labels := by rfl

def raw41784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41784Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41784 raw41784Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw41784 raw41784Labels = mixedMoment B raw41784step0 raw41784step0Labels := by
      have ha : raw41784step0 = raw41784 := by apply Matrix.ext; unfold raw41784step0 raw41784; decide +kernel
      have hl : raw41784Labels = labelEmbedding1 ∘ raw41784step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41784 raw41784Labels raw41784step0Labels labelEmbedding1 hl
    _ = mixedMoment B node2234 node2234Labels := by rfl

def raw41785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41785Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41785step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41785step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41785step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41785step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41785step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41785 raw41785Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw41785 raw41785Labels = mixedMoment B raw41785step0 raw41785step0Labels := by
      have ha : raw41785step0 = (fun i j => raw41785 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41785step0 raw41785; decide +kernel
      have hl : raw41785step0Labels = raw41785Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41785 raw41785Labels permutation246 permutation7
    mixedMoment B raw41785step0 raw41785step0Labels = mixedMoment B raw41785step1 raw41785step1Labels := by
      have ha : raw41785step1 = -raw41785step0 := by apply Matrix.ext; change ∀ i j, raw41785step1 i j = -(raw41785step0 i j); unfold raw41785step1 raw41785step0; decide +kernel
      have hl : raw41785step1Labels = raw41785step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41785step1 raw41785step1Labels = mixedMoment B raw41785step2 raw41785step2Labels := by
      have ha : raw41785step2 = raw41785step1 := by apply Matrix.ext; unfold raw41785step2 raw41785step1; decide +kernel
      have hl : raw41785step1Labels = labelEmbedding6 ∘ raw41785step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41785step1 raw41785step1Labels raw41785step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

def raw41786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41786Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41786 raw41786Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw41786 raw41786Labels = mixedMoment B raw41786step0 raw41786step0Labels := by
      have ha : raw41786step0 = raw41786 := by apply Matrix.ext; unfold raw41786step0 raw41786; decide +kernel
      have hl : raw41786Labels = labelEmbedding1 ∘ raw41786step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41786 raw41786Labels raw41786step0Labels labelEmbedding1 hl
    _ = mixedMoment B node2233 node2233Labels := by rfl

def raw41787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41787Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41787 raw41787Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw41787 raw41787Labels = mixedMoment B raw41787step0 raw41787step0Labels := by
      have ha : raw41787step0 = raw41787 := by apply Matrix.ext; unfold raw41787step0 raw41787; decide +kernel
      have hl : raw41787Labels = labelEmbedding8 ∘ raw41787step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41787 raw41787Labels raw41787step0Labels labelEmbedding8 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw41788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41788Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41788 raw41788Labels = mixedMoment B node2232 node2232Labels := by
  calc
    mixedMoment B raw41788 raw41788Labels = mixedMoment B raw41788step0 raw41788step0Labels := by
      have ha : raw41788step0 = raw41788 := by apply Matrix.ext; unfold raw41788step0 raw41788; decide +kernel
      have hl : raw41788Labels = labelEmbedding1 ∘ raw41788step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41788 raw41788Labels raw41788step0Labels labelEmbedding1 hl
    _ = mixedMoment B node2232 node2232Labels := by rfl

def raw41789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41789Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw41789step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41789step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41789step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41789step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41789 raw41789Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw41789 raw41789Labels = mixedMoment B raw41789step0 raw41789step0Labels := by
      have ha : raw41789step0 = (fun i j => raw41789 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41789step0 raw41789; decide +kernel
      have hl : raw41789step0Labels = raw41789Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41789 raw41789Labels permutation224 permutation7
    mixedMoment B raw41789step0 raw41789step0Labels = mixedMoment B raw41789step1 raw41789step1Labels := by
      have ha : raw41789step1 = -raw41789step0 := by apply Matrix.ext; change ∀ i j, raw41789step1 i j = -(raw41789step0 i j); unfold raw41789step1 raw41789step0; decide +kernel
      have hl : raw41789step1Labels = raw41789step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41789step1 raw41789step1Labels = mixedMoment B raw41789step2 raw41789step2Labels := by
      have ha : raw41789step2 = raw41789step1 := by apply Matrix.ext; unfold raw41789step2 raw41789step1; decide +kernel
      have hl : raw41789step1Labels = labelEmbedding6 ∘ raw41789step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41789step1 raw41789step1Labels raw41789step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

def raw41790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41790Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41790 raw41790Labels = mixedMoment B node2231 node2231Labels := by
  calc
    mixedMoment B raw41790 raw41790Labels = mixedMoment B raw41790step0 raw41790step0Labels := by
      have ha : raw41790step0 = raw41790 := by apply Matrix.ext; unfold raw41790step0 raw41790; decide +kernel
      have hl : raw41790Labels = labelEmbedding1 ∘ raw41790step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41790 raw41790Labels raw41790step0Labels labelEmbedding1 hl
    _ = mixedMoment B node2231 node2231Labels := by rfl

def raw41791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41791Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41791step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41791step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41791step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41791 raw41791Labels = mixedMoment B node4695 node4695Labels := by
  calc
    mixedMoment B raw41791 raw41791Labels = mixedMoment B raw41791step0 raw41791step0Labels := by
      have ha : raw41791step0 = (fun i j => raw41791 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41791step0 raw41791; decide +kernel
      have hl : raw41791step0Labels = raw41791Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41791 raw41791Labels permutation224 permutation7
    mixedMoment B raw41791step0 raw41791step0Labels = mixedMoment B raw41791step1 raw41791step1Labels := by
      have ha : raw41791step1 = -raw41791step0 := by apply Matrix.ext; change ∀ i j, raw41791step1 i j = -(raw41791step0 i j); unfold raw41791step1 raw41791step0; decide +kernel
      have hl : raw41791step1Labels = raw41791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41791step1 raw41791step1Labels = mixedMoment B raw41791step2 raw41791step2Labels := by
      have ha : raw41791step2 = raw41791step1 := by apply Matrix.ext; unfold raw41791step2 raw41791step1; decide +kernel
      have hl : raw41791step1Labels = labelEmbedding6 ∘ raw41791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41791step1 raw41791step1Labels raw41791step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4695 node4695Labels := by rfl

def raw41792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41792Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41792step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41792 raw41792Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw41792 raw41792Labels = mixedMoment B raw41792step0 raw41792step0Labels := by
      have hz : ∀ j, raw41792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41792step0 = (fun i j => raw41792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41792step0 raw41792; decide +kernel
      have hl : raw41792step0Labels = raw41792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41792 raw41792Labels permutation434 hz
    mixedMoment B raw41792step0 raw41792step0Labels = mixedMoment B raw41792step1 raw41792step1Labels := by
      have ha : raw41792step1 = raw41792step0 := by apply Matrix.ext; unfold raw41792step1 raw41792step0; decide +kernel
      have hl : raw41792step0Labels = labelEmbedding1 ∘ raw41792step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41792step0 raw41792step0Labels raw41792step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw41793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41793Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41793step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw41793step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41793step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41793step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41793step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41793 raw41793Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw41793 raw41793Labels = mixedMoment B raw41793step0 raw41793step0Labels := by
      have hz : ∀ j, raw41793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41793step0 = (fun i j => raw41793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41793step0 raw41793; decide +kernel
      have hl : raw41793step0Labels = raw41793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41793 raw41793Labels permutation434 hz
    mixedMoment B raw41793step0 raw41793step0Labels = mixedMoment B raw41793step1 raw41793step1Labels := by
      have ha : raw41793step1 = (fun i j => raw41793step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41793step1 raw41793step0; decide +kernel
      have hl : raw41793step1Labels = raw41793step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41793step0 raw41793step0Labels permutation50 permutation7
    mixedMoment B raw41793step1 raw41793step1Labels = mixedMoment B raw41793step2 raw41793step2Labels := by
      have ha : raw41793step2 = -raw41793step1 := by apply Matrix.ext; change ∀ i j, raw41793step2 i j = -(raw41793step1 i j); unfold raw41793step2 raw41793step1; decide +kernel
      have hl : raw41793step2Labels = raw41793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41793step2 raw41793step2Labels = mixedMoment B raw41793step3 raw41793step3Labels := by
      have ha : raw41793step3 = raw41793step2 := by apply Matrix.ext; unfold raw41793step3 raw41793step2; decide +kernel
      have hl : raw41793step2Labels = labelEmbedding6 ∘ raw41793step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41793step2 raw41793step2Labels raw41793step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw41794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41794Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41794step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41794 raw41794Labels = mixedMoment B node2239 node2239Labels := by
  calc
    mixedMoment B raw41794 raw41794Labels = mixedMoment B raw41794step0 raw41794step0Labels := by
      have hz : ∀ j, raw41794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41794step0 = (fun i j => raw41794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41794step0 raw41794; decide +kernel
      have hl : raw41794step0Labels = raw41794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41794 raw41794Labels permutation434 hz
    mixedMoment B raw41794step0 raw41794step0Labels = mixedMoment B raw41794step1 raw41794step1Labels := by
      have ha : raw41794step1 = raw41794step0 := by apply Matrix.ext; unfold raw41794step1 raw41794step0; decide +kernel
      have hl : raw41794step0Labels = labelEmbedding1 ∘ raw41794step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41794step0 raw41794step0Labels raw41794step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2239 node2239Labels := by rfl

def raw41795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41795Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41795step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw41795step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41795step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41795step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41795step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41795 raw41795Labels = mixedMoment B node4697 node4697Labels := by
  calc
    mixedMoment B raw41795 raw41795Labels = mixedMoment B raw41795step0 raw41795step0Labels := by
      have hz : ∀ j, raw41795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41795step0 = (fun i j => raw41795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41795step0 raw41795; decide +kernel
      have hl : raw41795step0Labels = raw41795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41795 raw41795Labels permutation434 hz
    mixedMoment B raw41795step0 raw41795step0Labels = mixedMoment B raw41795step1 raw41795step1Labels := by
      have ha : raw41795step1 = (fun i j => raw41795step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41795step1 raw41795step0; decide +kernel
      have hl : raw41795step1Labels = raw41795step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41795step0 raw41795step0Labels permutation44 permutation7
    mixedMoment B raw41795step1 raw41795step1Labels = mixedMoment B raw41795step2 raw41795step2Labels := by
      have ha : raw41795step2 = -raw41795step1 := by apply Matrix.ext; change ∀ i j, raw41795step2 i j = -(raw41795step1 i j); unfold raw41795step2 raw41795step1; decide +kernel
      have hl : raw41795step2Labels = raw41795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41795step2 raw41795step2Labels = mixedMoment B raw41795step3 raw41795step3Labels := by
      have ha : raw41795step3 = raw41795step2 := by apply Matrix.ext; unfold raw41795step3 raw41795step2; decide +kernel
      have hl : raw41795step2Labels = labelEmbedding6 ∘ raw41795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41795step2 raw41795step2Labels raw41795step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4697 node4697Labels := by rfl

def raw41796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41796Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41796 raw41796Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw41796 raw41796Labels = mixedMoment B raw41796step0 raw41796step0Labels := by
      have ha : raw41796step0 = (fun i j => raw41796 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41796step0 raw41796; decide +kernel
      have hl : raw41796step0Labels = raw41796Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41796 raw41796Labels permutation200 permutation2
    mixedMoment B raw41796step0 raw41796step0Labels = mixedMoment B raw41796step1 raw41796step1Labels := by
      have ha : raw41796step1 = raw41796step0 := by apply Matrix.ext; unfold raw41796step1 raw41796step0; decide +kernel
      have hl : raw41796step0Labels = labelEmbedding1 ∘ raw41796step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41796step0 raw41796step0Labels raw41796step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw41797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41797Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw41797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41797step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41797step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41797 raw41797Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw41797 raw41797Labels = mixedMoment B raw41797step0 raw41797step0Labels := by
      have ha : raw41797step0 = (fun i j => raw41797 (permutation218 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41797step0 raw41797; decide +kernel
      have hl : raw41797step0Labels = raw41797Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41797 raw41797Labels permutation218 permutation7
    mixedMoment B raw41797step0 raw41797step0Labels = mixedMoment B raw41797step1 raw41797step1Labels := by
      have ha : raw41797step1 = -raw41797step0 := by apply Matrix.ext; change ∀ i j, raw41797step1 i j = -(raw41797step0 i j); unfold raw41797step1 raw41797step0; decide +kernel
      have hl : raw41797step1Labels = raw41797step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41797step1 raw41797step1Labels = mixedMoment B raw41797step2 raw41797step2Labels := by
      have ha : raw41797step2 = raw41797step1 := by apply Matrix.ext; unfold raw41797step2 raw41797step1; decide +kernel
      have hl : raw41797step1Labels = labelEmbedding6 ∘ raw41797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41797step1 raw41797step1Labels raw41797step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw41798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41798Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41798 raw41798Labels = mixedMoment B node2189 node2189Labels := by
  calc
    mixedMoment B raw41798 raw41798Labels = mixedMoment B raw41798step0 raw41798step0Labels := by
      have ha : raw41798step0 = (fun i j => raw41798 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41798step0 raw41798; decide +kernel
      have hl : raw41798step0Labels = raw41798Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41798 raw41798Labels permutation200 permutation2
    mixedMoment B raw41798step0 raw41798step0Labels = mixedMoment B raw41798step1 raw41798step1Labels := by
      have ha : raw41798step1 = raw41798step0 := by apply Matrix.ext; unfold raw41798step1 raw41798step0; decide +kernel
      have hl : raw41798step0Labels = labelEmbedding1 ∘ raw41798step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41798step0 raw41798step0Labels raw41798step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2189 node2189Labels := by rfl

def raw41799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41799Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw41799step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41799step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41799step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41799step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41799 raw41799Labels = mixedMoment B node4771 node4771Labels := by
  calc
    mixedMoment B raw41799 raw41799Labels = mixedMoment B raw41799step0 raw41799step0Labels := by
      have ha : raw41799step0 = (fun i j => raw41799 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41799step0 raw41799; decide +kernel
      have hl : raw41799step0Labels = raw41799Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41799 raw41799Labels permutation212 permutation7
    mixedMoment B raw41799step0 raw41799step0Labels = mixedMoment B raw41799step1 raw41799step1Labels := by
      have ha : raw41799step1 = -raw41799step0 := by apply Matrix.ext; change ∀ i j, raw41799step1 i j = -(raw41799step0 i j); unfold raw41799step1 raw41799step0; decide +kernel
      have hl : raw41799step1Labels = raw41799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41799step1 raw41799step1Labels = mixedMoment B raw41799step2 raw41799step2Labels := by
      have ha : raw41799step2 = raw41799step1 := by apply Matrix.ext; unfold raw41799step2 raw41799step1; decide +kernel
      have hl : raw41799step1Labels = labelEmbedding6 ∘ raw41799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41799step1 raw41799step1Labels raw41799step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4771 node4771Labels := by rfl

def raw41800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41800Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41800 raw41800Labels = mixedMoment B node2140 node2140Labels := by
  calc
    mixedMoment B raw41800 raw41800Labels = mixedMoment B raw41800step0 raw41800step0Labels := by
      have ha : raw41800step0 = (fun i j => raw41800 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41800step0 raw41800; decide +kernel
      have hl : raw41800step0Labels = raw41800Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41800 raw41800Labels permutation200 permutation2
    mixedMoment B raw41800step0 raw41800step0Labels = mixedMoment B raw41800step1 raw41800step1Labels := by
      have ha : raw41800step1 = raw41800step0 := by apply Matrix.ext; unfold raw41800step1 raw41800step0; decide +kernel
      have hl : raw41800step0Labels = labelEmbedding1 ∘ raw41800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41800step0 raw41800step0Labels raw41800step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2140 node2140Labels := by rfl

def raw41801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41801Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw41801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41801step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41801step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41801 raw41801Labels = mixedMoment B node4663 node4663Labels := by
  calc
    mixedMoment B raw41801 raw41801Labels = mixedMoment B raw41801step0 raw41801step0Labels := by
      have ha : raw41801step0 = (fun i j => raw41801 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41801step0 raw41801; decide +kernel
      have hl : raw41801step0Labels = raw41801Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41801 raw41801Labels permutation212 permutation7
    mixedMoment B raw41801step0 raw41801step0Labels = mixedMoment B raw41801step1 raw41801step1Labels := by
      have ha : raw41801step1 = -raw41801step0 := by apply Matrix.ext; change ∀ i j, raw41801step1 i j = -(raw41801step0 i j); unfold raw41801step1 raw41801step0; decide +kernel
      have hl : raw41801step1Labels = raw41801step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41801step1 raw41801step1Labels = mixedMoment B raw41801step2 raw41801step2Labels := by
      have ha : raw41801step2 = raw41801step1 := by apply Matrix.ext; unfold raw41801step2 raw41801step1; decide +kernel
      have hl : raw41801step1Labels = labelEmbedding6 ∘ raw41801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41801step1 raw41801step1Labels raw41801step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4663 node4663Labels := by rfl

def raw41802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41802Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41802 raw41802Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw41802 raw41802Labels = mixedMoment B raw41802step0 raw41802step0Labels := by
      have ha : raw41802step0 = (fun i j => raw41802 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41802step0 raw41802; decide +kernel
      have hl : raw41802step0Labels = raw41802Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41802 raw41802Labels permutation157 permutation2
    mixedMoment B raw41802step0 raw41802step0Labels = mixedMoment B raw41802step1 raw41802step1Labels := by
      have ha : raw41802step1 = raw41802step0 := by apply Matrix.ext; unfold raw41802step1 raw41802step0; decide +kernel
      have hl : raw41802step0Labels = labelEmbedding1 ∘ raw41802step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41802step0 raw41802step0Labels raw41802step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

def raw41803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41803Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw41803step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41803step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41803step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41803 raw41803Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw41803 raw41803Labels = mixedMoment B raw41803step0 raw41803step0Labels := by
      have ha : raw41803step0 = (fun i j => raw41803 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41803step0 raw41803; decide +kernel
      have hl : raw41803step0Labels = raw41803Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41803 raw41803Labels permutation247 permutation7
    mixedMoment B raw41803step0 raw41803step0Labels = mixedMoment B raw41803step1 raw41803step1Labels := by
      have ha : raw41803step1 = -raw41803step0 := by apply Matrix.ext; change ∀ i j, raw41803step1 i j = -(raw41803step0 i j); unfold raw41803step1 raw41803step0; decide +kernel
      have hl : raw41803step1Labels = raw41803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41803step1 raw41803step1Labels = mixedMoment B raw41803step2 raw41803step2Labels := by
      have ha : raw41803step2 = raw41803step1 := by apply Matrix.ext; unfold raw41803step2 raw41803step1; decide +kernel
      have hl : raw41803step1Labels = labelEmbedding6 ∘ raw41803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41803step1 raw41803step1Labels raw41803step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4696 node4696Labels := by rfl

def raw41804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41804Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41804step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41804 raw41804Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw41804 raw41804Labels = mixedMoment B raw41804step0 raw41804step0Labels := by
      have ha : raw41804step0 = (fun i j => raw41804 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41804step0 raw41804; decide +kernel
      have hl : raw41804step0Labels = raw41804Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41804 raw41804Labels permutation157 permutation2
    mixedMoment B raw41804step0 raw41804step0Labels = mixedMoment B raw41804step1 raw41804step1Labels := by
      have ha : raw41804step1 = raw41804step0 := by apply Matrix.ext; unfold raw41804step1 raw41804step0; decide +kernel
      have hl : raw41804step0Labels = labelEmbedding1 ∘ raw41804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41804step0 raw41804step0Labels raw41804step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw41805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41805Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw41805step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41805step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41805step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41805step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41805 raw41805Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw41805 raw41805Labels = mixedMoment B raw41805step0 raw41805step0Labels := by
      have ha : raw41805step0 = (fun i j => raw41805 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41805step0 raw41805; decide +kernel
      have hl : raw41805step0Labels = raw41805Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41805 raw41805Labels permutation260 permutation7
    mixedMoment B raw41805step0 raw41805step0Labels = mixedMoment B raw41805step1 raw41805step1Labels := by
      have ha : raw41805step1 = -raw41805step0 := by apply Matrix.ext; change ∀ i j, raw41805step1 i j = -(raw41805step0 i j); unfold raw41805step1 raw41805step0; decide +kernel
      have hl : raw41805step1Labels = raw41805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41805step1 raw41805step1Labels = mixedMoment B raw41805step2 raw41805step2Labels := by
      have ha : raw41805step2 = raw41805step1 := by apply Matrix.ext; unfold raw41805step2 raw41805step1; decide +kernel
      have hl : raw41805step1Labels = labelEmbedding6 ∘ raw41805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41805step1 raw41805step1Labels raw41805step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw41806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41806Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw41806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw41806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41806 raw41806Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw41806 raw41806Labels = mixedMoment B raw41806step0 raw41806step0Labels := by
      have hz : ∀ j, raw41806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41806step0 = (fun i j => raw41806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41806step0 raw41806; decide +kernel
      have hl : raw41806step0Labels = raw41806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41806 raw41806Labels permutation434 hz
    mixedMoment B raw41806step0 raw41806step0Labels = mixedMoment B raw41806step1 raw41806step1Labels := by
      have hz : ∀ j, raw41806step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41806step1 = (fun i j => raw41806step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41806step1 raw41806step0; decide +kernel
      have hl : raw41806step1Labels = raw41806step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41806step0 raw41806step0Labels permutation80 hz
    mixedMoment B raw41806step1 raw41806step1Labels = mixedMoment B raw41806step2 raw41806step2Labels := by
      have ha : raw41806step2 = raw41806step1 := by apply Matrix.ext; unfold raw41806step2 raw41806step1; decide +kernel
      have hl : raw41806step1Labels = labelEmbedding1 ∘ raw41806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41806step1 raw41806step1Labels raw41806step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw41807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41807Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41807step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw41807step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41807step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw41807step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41807step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41807step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41807step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41807step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41807 raw41807Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw41807 raw41807Labels = mixedMoment B raw41807step0 raw41807step0Labels := by
      have hz : ∀ j, raw41807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41807step0 = (fun i j => raw41807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41807step0 raw41807; decide +kernel
      have hl : raw41807step0Labels = raw41807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41807 raw41807Labels permutation434 hz
    mixedMoment B raw41807step0 raw41807step0Labels = mixedMoment B raw41807step1 raw41807step1Labels := by
      have hz : ∀ j, raw41807step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41807step1 = (fun i j => raw41807step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41807step1 raw41807step0; decide +kernel
      have hl : raw41807step1Labels = raw41807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41807step0 raw41807step0Labels permutation80 hz
    mixedMoment B raw41807step1 raw41807step1Labels = mixedMoment B raw41807step2 raw41807step2Labels := by
      have ha : raw41807step2 = (fun i j => raw41807step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41807step2 raw41807step1; decide +kernel
      have hl : raw41807step2Labels = raw41807step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41807step1 raw41807step1Labels permutation12 permutation7
    mixedMoment B raw41807step2 raw41807step2Labels = mixedMoment B raw41807step3 raw41807step3Labels := by
      have ha : raw41807step3 = -raw41807step2 := by apply Matrix.ext; change ∀ i j, raw41807step3 i j = -(raw41807step2 i j); unfold raw41807step3 raw41807step2; decide +kernel
      have hl : raw41807step3Labels = raw41807step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41807step3 raw41807step3Labels = mixedMoment B raw41807step4 raw41807step4Labels := by
      have ha : raw41807step4 = raw41807step3 := by apply Matrix.ext; unfold raw41807step4 raw41807step3; decide +kernel
      have hl : raw41807step3Labels = labelEmbedding6 ∘ raw41807step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41807step3 raw41807step3Labels raw41807step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw41808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41808Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw41808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw41808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41808 raw41808Labels = mixedMoment B node2258 node2258Labels := by
  calc
    mixedMoment B raw41808 raw41808Labels = mixedMoment B raw41808step0 raw41808step0Labels := by
      have hz : ∀ j, raw41808 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41808step0 = (fun i j => raw41808 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41808step0 raw41808; decide +kernel
      have hl : raw41808step0Labels = raw41808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41808 raw41808Labels permutation434 hz
    mixedMoment B raw41808step0 raw41808step0Labels = mixedMoment B raw41808step1 raw41808step1Labels := by
      have hz : ∀ j, raw41808step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41808step1 = (fun i j => raw41808step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41808step1 raw41808step0; decide +kernel
      have hl : raw41808step1Labels = raw41808step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41808step0 raw41808step0Labels permutation80 hz
    mixedMoment B raw41808step1 raw41808step1Labels = mixedMoment B raw41808step2 raw41808step2Labels := by
      have ha : raw41808step2 = raw41808step1 := by apply Matrix.ext; unfold raw41808step2 raw41808step1; decide +kernel
      have hl : raw41808step1Labels = labelEmbedding1 ∘ raw41808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41808step1 raw41808step1Labels raw41808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2258 node2258Labels := by rfl

def raw41809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41809Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41809step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw41809step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw41809step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41809 raw41809Labels = mixedMoment B node4560 node4560Labels := by
  calc
    mixedMoment B raw41809 raw41809Labels = mixedMoment B raw41809step0 raw41809step0Labels := by
      have hz : ∀ j, raw41809 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41809step0 = (fun i j => raw41809 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41809step0 raw41809; decide +kernel
      have hl : raw41809step0Labels = raw41809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41809 raw41809Labels permutation434 hz
    mixedMoment B raw41809step0 raw41809step0Labels = mixedMoment B raw41809step1 raw41809step1Labels := by
      have hz : ∀ j, raw41809step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41809step1 = (fun i j => raw41809step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41809step1 raw41809step0; decide +kernel
      have hl : raw41809step1Labels = raw41809step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41809step0 raw41809step0Labels permutation80 hz
    mixedMoment B raw41809step1 raw41809step1Labels = mixedMoment B raw41809step2 raw41809step2Labels := by
      have ha : raw41809step2 = (fun i j => raw41809step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41809step2 raw41809step1; decide +kernel
      have hl : raw41809step2Labels = raw41809step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41809step1 raw41809step1Labels permutation29 permutation6
    _ = mixedMoment B node4560 node4560Labels := by rfl

def raw41810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41810Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41810step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw41810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw41810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41810 raw41810Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw41810 raw41810Labels = mixedMoment B raw41810step0 raw41810step0Labels := by
      have hz : ∀ j, raw41810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41810step0 = (fun i j => raw41810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41810step0 raw41810; decide +kernel
      have hl : raw41810step0Labels = raw41810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41810 raw41810Labels permutation346 hz
    mixedMoment B raw41810step0 raw41810step0Labels = mixedMoment B raw41810step1 raw41810step1Labels := by
      have ha : raw41810step1 = (fun i j => raw41810step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41810step1 raw41810step0; decide +kernel
      have hl : raw41810step1Labels = raw41810step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41810step0 raw41810step0Labels permutation38 permutation2
    mixedMoment B raw41810step1 raw41810step1Labels = mixedMoment B raw41810step2 raw41810step2Labels := by
      have ha : raw41810step2 = raw41810step1 := by apply Matrix.ext; unfold raw41810step2 raw41810step1; decide +kernel
      have hl : raw41810step1Labels = labelEmbedding1 ∘ raw41810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41810step1 raw41810step1Labels raw41810step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw41811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41811Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41811step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw41811step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41811step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41811step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41811step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41811 raw41811Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw41811 raw41811Labels = mixedMoment B raw41811step0 raw41811step0Labels := by
      have hz : ∀ j, raw41811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41811step0 = (fun i j => raw41811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41811step0 raw41811; decide +kernel
      have hl : raw41811step0Labels = raw41811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41811 raw41811Labels permutation346 hz
    mixedMoment B raw41811step0 raw41811step0Labels = mixedMoment B raw41811step1 raw41811step1Labels := by
      have ha : raw41811step1 = (fun i j => raw41811step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41811step1 raw41811step0; decide +kernel
      have hl : raw41811step1Labels = raw41811step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41811step0 raw41811step0Labels permutation42 permutation7
    mixedMoment B raw41811step1 raw41811step1Labels = mixedMoment B raw41811step2 raw41811step2Labels := by
      have ha : raw41811step2 = -raw41811step1 := by apply Matrix.ext; change ∀ i j, raw41811step2 i j = -(raw41811step1 i j); unfold raw41811step2 raw41811step1; decide +kernel
      have hl : raw41811step2Labels = raw41811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41811step2 raw41811step2Labels = mixedMoment B raw41811step3 raw41811step3Labels := by
      have ha : raw41811step3 = raw41811step2 := by apply Matrix.ext; unfold raw41811step3 raw41811step2; decide +kernel
      have hl : raw41811step2Labels = labelEmbedding6 ∘ raw41811step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41811step2 raw41811step2Labels raw41811step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw41812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41812Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw41812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw41812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41812 raw41812Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw41812 raw41812Labels = mixedMoment B raw41812step0 raw41812step0Labels := by
      have hz : ∀ j, raw41812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41812step0 = (fun i j => raw41812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41812step0 raw41812; decide +kernel
      have hl : raw41812step0Labels = raw41812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41812 raw41812Labels permutation346 hz
    mixedMoment B raw41812step0 raw41812step0Labels = mixedMoment B raw41812step1 raw41812step1Labels := by
      have ha : raw41812step1 = (fun i j => raw41812step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41812step1 raw41812step0; decide +kernel
      have hl : raw41812step1Labels = raw41812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41812step0 raw41812step0Labels permutation38 permutation2
    mixedMoment B raw41812step1 raw41812step1Labels = mixedMoment B raw41812step2 raw41812step2Labels := by
      have ha : raw41812step2 = raw41812step1 := by apply Matrix.ext; unfold raw41812step2 raw41812step1; decide +kernel
      have hl : raw41812step1Labels = labelEmbedding1 ∘ raw41812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41812step1 raw41812step1Labels raw41812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

def raw41813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41813Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41813step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41813 raw41813Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw41813 raw41813Labels = mixedMoment B raw41813step0 raw41813step0Labels := by
      have hz : ∀ j, raw41813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41813step0 = (fun i j => raw41813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41813step0 raw41813; decide +kernel
      have hl : raw41813step0Labels = raw41813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41813 raw41813Labels permutation346 hz
    mixedMoment B raw41813step0 raw41813step0Labels = mixedMoment B raw41813step1 raw41813step1Labels := by
      have ha : raw41813step1 = (fun i j => raw41813step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41813step1 raw41813step0; decide +kernel
      have hl : raw41813step1Labels = raw41813step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41813step0 raw41813step0Labels permutation137 permutation6
    _ = mixedMoment B node4552 node4552Labels := by rfl

def raw41814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41814Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41814 raw41814Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw41814 raw41814Labels = mixedMoment B raw41814step0 raw41814step0Labels := by
      have hz : ∀ j, raw41814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41814step0 = (fun i j => raw41814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41814step0 raw41814; decide +kernel
      have hl : raw41814step0Labels = raw41814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41814 raw41814Labels permutation346 hz
    mixedMoment B raw41814step0 raw41814step0Labels = mixedMoment B raw41814step1 raw41814step1Labels := by
      have ha : raw41814step1 = (fun i j => raw41814step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41814step1 raw41814step0; decide +kernel
      have hl : raw41814step1Labels = raw41814step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41814step0 raw41814step0Labels permutation38 permutation2
    mixedMoment B raw41814step1 raw41814step1Labels = mixedMoment B raw41814step2 raw41814step2Labels := by
      have ha : raw41814step2 = raw41814step1 := by apply Matrix.ext; unfold raw41814step2 raw41814step1; decide +kernel
      have hl : raw41814step1Labels = labelEmbedding1 ∘ raw41814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41814step1 raw41814step1Labels raw41814step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2149 node2149Labels := by rfl

def raw41815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41815Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41815step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41815 raw41815Labels = mixedMoment B node4536 node4536Labels := by
  calc
    mixedMoment B raw41815 raw41815Labels = mixedMoment B raw41815step0 raw41815step0Labels := by
      have hz : ∀ j, raw41815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41815step0 = (fun i j => raw41815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41815step0 raw41815; decide +kernel
      have hl : raw41815step0Labels = raw41815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41815 raw41815Labels permutation346 hz
    mixedMoment B raw41815step0 raw41815step0Labels = mixedMoment B raw41815step1 raw41815step1Labels := by
      have ha : raw41815step1 = (fun i j => raw41815step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41815step1 raw41815step0; decide +kernel
      have hl : raw41815step1Labels = raw41815step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41815step0 raw41815step0Labels permutation139 permutation6
    _ = mixedMoment B node4536 node4536Labels := by rfl

def raw41816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41816Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw41816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw41816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41816 raw41816Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw41816 raw41816Labels = mixedMoment B raw41816step0 raw41816step0Labels := by
      have hz : ∀ j, raw41816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41816step0 = (fun i j => raw41816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41816step0 raw41816; decide +kernel
      have hl : raw41816step0Labels = raw41816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41816 raw41816Labels permutation346 hz
    mixedMoment B raw41816step0 raw41816step0Labels = mixedMoment B raw41816step1 raw41816step1Labels := by
      have ha : raw41816step1 = (fun i j => raw41816step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41816step1 raw41816step0; decide +kernel
      have hl : raw41816step1Labels = raw41816step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41816step0 raw41816step0Labels permutation37 permutation2
    mixedMoment B raw41816step1 raw41816step1Labels = mixedMoment B raw41816step2 raw41816step2Labels := by
      have ha : raw41816step2 = raw41816step1 := by apply Matrix.ext; unfold raw41816step2 raw41816step1; decide +kernel
      have hl : raw41816step1Labels = labelEmbedding1 ∘ raw41816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41816step1 raw41816step1Labels raw41816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

def raw41817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41817Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41817step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw41817step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41817step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41817step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41817step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41817 raw41817Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw41817 raw41817Labels = mixedMoment B raw41817step0 raw41817step0Labels := by
      have hz : ∀ j, raw41817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41817step0 = (fun i j => raw41817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41817step0 raw41817; decide +kernel
      have hl : raw41817step0Labels = raw41817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41817 raw41817Labels permutation346 hz
    mixedMoment B raw41817step0 raw41817step0Labels = mixedMoment B raw41817step1 raw41817step1Labels := by
      have ha : raw41817step1 = (fun i j => raw41817step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41817step1 raw41817step0; decide +kernel
      have hl : raw41817step1Labels = raw41817step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41817step0 raw41817step0Labels permutation51 permutation7
    mixedMoment B raw41817step1 raw41817step1Labels = mixedMoment B raw41817step2 raw41817step2Labels := by
      have ha : raw41817step2 = -raw41817step1 := by apply Matrix.ext; change ∀ i j, raw41817step2 i j = -(raw41817step1 i j); unfold raw41817step2 raw41817step1; decide +kernel
      have hl : raw41817step2Labels = raw41817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41817step2 raw41817step2Labels = mixedMoment B raw41817step3 raw41817step3Labels := by
      have ha : raw41817step3 = raw41817step2 := by apply Matrix.ext; unfold raw41817step3 raw41817step2; decide +kernel
      have hl : raw41817step2Labels = labelEmbedding6 ∘ raw41817step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41817step2 raw41817step2Labels raw41817step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4699 node4699Labels := by rfl

def raw41818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41818Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41818step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw41818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw41818step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41818 raw41818Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw41818 raw41818Labels = mixedMoment B raw41818step0 raw41818step0Labels := by
      have hz : ∀ j, raw41818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41818step0 = (fun i j => raw41818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41818step0 raw41818; decide +kernel
      have hl : raw41818step0Labels = raw41818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41818 raw41818Labels permutation346 hz
    mixedMoment B raw41818step0 raw41818step0Labels = mixedMoment B raw41818step1 raw41818step1Labels := by
      have ha : raw41818step1 = (fun i j => raw41818step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41818step1 raw41818step0; decide +kernel
      have hl : raw41818step1Labels = raw41818step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41818step0 raw41818step0Labels permutation37 permutation2
    mixedMoment B raw41818step1 raw41818step1Labels = mixedMoment B raw41818step2 raw41818step2Labels := by
      have ha : raw41818step2 = raw41818step1 := by apply Matrix.ext; unfold raw41818step2 raw41818step1; decide +kernel
      have hl : raw41818step1Labels = labelEmbedding1 ∘ raw41818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41818step1 raw41818step1Labels raw41818step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw41819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41819Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41819step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw41819step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41819step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41819step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41819step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41819 raw41819Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw41819 raw41819Labels = mixedMoment B raw41819step0 raw41819step0Labels := by
      have hz : ∀ j, raw41819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41819step0 = (fun i j => raw41819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41819step0 raw41819; decide +kernel
      have hl : raw41819step0Labels = raw41819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41819 raw41819Labels permutation346 hz
    mixedMoment B raw41819step0 raw41819step0Labels = mixedMoment B raw41819step1 raw41819step1Labels := by
      have ha : raw41819step1 = (fun i j => raw41819step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41819step1 raw41819step0; decide +kernel
      have hl : raw41819step1Labels = raw41819step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41819step0 raw41819step0Labels permutation54 permutation7
    mixedMoment B raw41819step1 raw41819step1Labels = mixedMoment B raw41819step2 raw41819step2Labels := by
      have ha : raw41819step2 = -raw41819step1 := by apply Matrix.ext; change ∀ i j, raw41819step2 i j = -(raw41819step1 i j); unfold raw41819step2 raw41819step1; decide +kernel
      have hl : raw41819step2Labels = raw41819step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41819step2 raw41819step2Labels = mixedMoment B raw41819step3 raw41819step3Labels := by
      have ha : raw41819step3 = raw41819step2 := by apply Matrix.ext; unfold raw41819step3 raw41819step2; decide +kernel
      have hl : raw41819step2Labels = labelEmbedding6 ∘ raw41819step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41819step2 raw41819step2Labels raw41819step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw41820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41820Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41820 raw41820Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw41820 raw41820Labels = mixedMoment B raw41820step0 raw41820step0Labels := by
      have hz : ∀ j, raw41820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41820step0 = (fun i j => raw41820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41820step0 raw41820; decide +kernel
      have hl : raw41820step0Labels = raw41820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41820 raw41820Labels permutation346 hz
    mixedMoment B raw41820step0 raw41820step0Labels = mixedMoment B raw41820step1 raw41820step1Labels := by
      have ha : raw41820step1 = (fun i j => raw41820step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41820step1 raw41820step0; decide +kernel
      have hl : raw41820step1Labels = raw41820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41820step0 raw41820step0Labels permutation36 permutation2
    mixedMoment B raw41820step1 raw41820step1Labels = mixedMoment B raw41820step2 raw41820step2Labels := by
      have ha : raw41820step2 = raw41820step1 := by apply Matrix.ext; unfold raw41820step2 raw41820step1; decide +kernel
      have hl : raw41820step1Labels = labelEmbedding1 ∘ raw41820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41820step1 raw41820step1Labels raw41820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2257 node2257Labels := by rfl

def raw41821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41821Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41821step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw41821step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41821step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41821step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41821step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41821 raw41821Labels = mixedMoment B node4701 node4701Labels := by
  calc
    mixedMoment B raw41821 raw41821Labels = mixedMoment B raw41821step0 raw41821step0Labels := by
      have hz : ∀ j, raw41821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41821step0 = (fun i j => raw41821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41821step0 raw41821; decide +kernel
      have hl : raw41821step0Labels = raw41821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41821 raw41821Labels permutation346 hz
    mixedMoment B raw41821step0 raw41821step0Labels = mixedMoment B raw41821step1 raw41821step1Labels := by
      have ha : raw41821step1 = (fun i j => raw41821step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41821step1 raw41821step0; decide +kernel
      have hl : raw41821step1Labels = raw41821step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41821step0 raw41821step0Labels permutation50 permutation7
    mixedMoment B raw41821step1 raw41821step1Labels = mixedMoment B raw41821step2 raw41821step2Labels := by
      have ha : raw41821step2 = -raw41821step1 := by apply Matrix.ext; change ∀ i j, raw41821step2 i j = -(raw41821step1 i j); unfold raw41821step2 raw41821step1; decide +kernel
      have hl : raw41821step2Labels = raw41821step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41821step2 raw41821step2Labels = mixedMoment B raw41821step3 raw41821step3Labels := by
      have ha : raw41821step3 = raw41821step2 := by apply Matrix.ext; unfold raw41821step3 raw41821step2; decide +kernel
      have hl : raw41821step2Labels = labelEmbedding6 ∘ raw41821step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41821step2 raw41821step2Labels raw41821step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4701 node4701Labels := by rfl

def raw41822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41822Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41822step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41822 raw41822Labels = mixedMoment B node2172 node2172Labels := by
  calc
    mixedMoment B raw41822 raw41822Labels = mixedMoment B raw41822step0 raw41822step0Labels := by
      have ha : raw41822step0 = (fun i j => raw41822 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41822step0 raw41822; decide +kernel
      have hl : raw41822step0Labels = raw41822Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41822 raw41822Labels permutation182 permutation2
    mixedMoment B raw41822step0 raw41822step0Labels = mixedMoment B raw41822step1 raw41822step1Labels := by
      have ha : raw41822step1 = raw41822step0 := by apply Matrix.ext; unfold raw41822step1 raw41822step0; decide +kernel
      have hl : raw41822step0Labels = labelEmbedding1 ∘ raw41822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41822step0 raw41822step0Labels raw41822step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2172 node2172Labels := by rfl

def raw41823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41823Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41823 raw41823Labels = mixedMoment B node4532 node4532Labels := by
  calc
    mixedMoment B raw41823 raw41823Labels = mixedMoment B raw41823step0 raw41823step0Labels := by
      have ha : raw41823step0 = (fun i j => raw41823 (permutation620 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41823step0 raw41823; decide +kernel
      have hl : raw41823step0Labels = raw41823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41823 raw41823Labels permutation620 permutation6
    _ = mixedMoment B node4532 node4532Labels := by rfl

def raw41824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41824Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw41824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw41824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41824 raw41824Labels = mixedMoment B node2198 node2198Labels := by
  calc
    mixedMoment B raw41824 raw41824Labels = mixedMoment B raw41824step0 raw41824step0Labels := by
      have ha : raw41824step0 = (fun i j => raw41824 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41824step0 raw41824; decide +kernel
      have hl : raw41824step0Labels = raw41824Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41824 raw41824Labels permutation181 permutation2
    mixedMoment B raw41824step0 raw41824step0Labels = mixedMoment B raw41824step1 raw41824step1Labels := by
      have ha : raw41824step1 = raw41824step0 := by apply Matrix.ext; unfold raw41824step1 raw41824step0; decide +kernel
      have hl : raw41824step0Labels = labelEmbedding1 ∘ raw41824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41824step0 raw41824step0Labels raw41824step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2198 node2198Labels := by rfl

def raw41825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41825Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw41825step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41825step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41825step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41825 raw41825Labels = mixedMoment B node4772 node4772Labels := by
  calc
    mixedMoment B raw41825 raw41825Labels = mixedMoment B raw41825step0 raw41825step0Labels := by
      have ha : raw41825step0 = (fun i j => raw41825 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41825step0 raw41825; decide +kernel
      have hl : raw41825step0Labels = raw41825Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41825 raw41825Labels permutation195 permutation7
    mixedMoment B raw41825step0 raw41825step0Labels = mixedMoment B raw41825step1 raw41825step1Labels := by
      have ha : raw41825step1 = -raw41825step0 := by apply Matrix.ext; change ∀ i j, raw41825step1 i j = -(raw41825step0 i j); unfold raw41825step1 raw41825step0; decide +kernel
      have hl : raw41825step1Labels = raw41825step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41825step1 raw41825step1Labels = mixedMoment B raw41825step2 raw41825step2Labels := by
      have ha : raw41825step2 = raw41825step1 := by apply Matrix.ext; unfold raw41825step2 raw41825step1; decide +kernel
      have hl : raw41825step1Labels = labelEmbedding6 ∘ raw41825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41825step1 raw41825step1Labels raw41825step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4772 node4772Labels := by rfl

def raw41826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41826Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41826step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41826 raw41826Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw41826 raw41826Labels = mixedMoment B raw41826step0 raw41826step0Labels := by
      have ha : raw41826step0 = (fun i j => raw41826 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41826step0 raw41826; decide +kernel
      have hl : raw41826step0Labels = raw41826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41826 raw41826Labels permutation179 permutation2
    mixedMoment B raw41826step0 raw41826step0Labels = mixedMoment B raw41826step1 raw41826step1Labels := by
      have ha : raw41826step1 = raw41826step0 := by apply Matrix.ext; unfold raw41826step1 raw41826step0; decide +kernel
      have hl : raw41826step0Labels = labelEmbedding1 ∘ raw41826step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41826step0 raw41826step0Labels raw41826step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw41827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41827Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw41827step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41827step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41827step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41827step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41827 raw41827Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw41827 raw41827Labels = mixedMoment B raw41827step0 raw41827step0Labels := by
      have ha : raw41827step0 = (fun i j => raw41827 (permutation192 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41827step0 raw41827; decide +kernel
      have hl : raw41827step0Labels = raw41827Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41827 raw41827Labels permutation192 permutation7
    mixedMoment B raw41827step0 raw41827step0Labels = mixedMoment B raw41827step1 raw41827step1Labels := by
      have ha : raw41827step1 = -raw41827step0 := by apply Matrix.ext; change ∀ i j, raw41827step1 i j = -(raw41827step0 i j); unfold raw41827step1 raw41827step0; decide +kernel
      have hl : raw41827step1Labels = raw41827step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41827step1 raw41827step1Labels = mixedMoment B raw41827step2 raw41827step2Labels := by
      have ha : raw41827step2 = raw41827step1 := by apply Matrix.ext; unfold raw41827step2 raw41827step1; decide +kernel
      have hl : raw41827step1Labels = labelEmbedding6 ∘ raw41827step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41827step1 raw41827step1Labels raw41827step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw41828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41828Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41828step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41828 raw41828Labels = mixedMoment B node2199 node2199Labels := by
  calc
    mixedMoment B raw41828 raw41828Labels = mixedMoment B raw41828step0 raw41828step0Labels := by
      have ha : raw41828step0 = (fun i j => raw41828 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41828step0 raw41828; decide +kernel
      have hl : raw41828step0Labels = raw41828Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41828 raw41828Labels permutation180 permutation2
    mixedMoment B raw41828step0 raw41828step0Labels = mixedMoment B raw41828step1 raw41828step1Labels := by
      have ha : raw41828step1 = raw41828step0 := by apply Matrix.ext; unfold raw41828step1 raw41828step0; decide +kernel
      have hl : raw41828step0Labels = labelEmbedding1 ∘ raw41828step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41828step0 raw41828step0Labels raw41828step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2199 node2199Labels := by rfl

def raw41829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41829Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw41829step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41829step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41829step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41829step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41829 raw41829Labels = mixedMoment B node4774 node4774Labels := by
  calc
    mixedMoment B raw41829 raw41829Labels = mixedMoment B raw41829step0 raw41829step0Labels := by
      have ha : raw41829step0 = (fun i j => raw41829 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41829step0 raw41829; decide +kernel
      have hl : raw41829step0Labels = raw41829Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41829 raw41829Labels permutation194 permutation7
    mixedMoment B raw41829step0 raw41829step0Labels = mixedMoment B raw41829step1 raw41829step1Labels := by
      have ha : raw41829step1 = -raw41829step0 := by apply Matrix.ext; change ∀ i j, raw41829step1 i j = -(raw41829step0 i j); unfold raw41829step1 raw41829step0; decide +kernel
      have hl : raw41829step1Labels = raw41829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41829step1 raw41829step1Labels = mixedMoment B raw41829step2 raw41829step2Labels := by
      have ha : raw41829step2 = raw41829step1 := by apply Matrix.ext; unfold raw41829step2 raw41829step1; decide +kernel
      have hl : raw41829step1Labels = labelEmbedding6 ∘ raw41829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41829step1 raw41829step1Labels raw41829step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4774 node4774Labels := by rfl

def raw41830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41830Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41830 raw41830Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw41830 raw41830Labels = mixedMoment B raw41830step0 raw41830step0Labels := by
      have ha : raw41830step0 = (fun i j => raw41830 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41830step0 raw41830; decide +kernel
      have hl : raw41830step0Labels = raw41830Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41830 raw41830Labels permutation181 permutation2
    mixedMoment B raw41830step0 raw41830step0Labels = mixedMoment B raw41830step1 raw41830step1Labels := by
      have ha : raw41830step1 = raw41830step0 := by apply Matrix.ext; unfold raw41830step1 raw41830step0; decide +kernel
      have hl : raw41830step0Labels = labelEmbedding1 ∘ raw41830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41830step0 raw41830step0Labels raw41830step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2147 node2147Labels := by rfl

def raw41831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41831Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw41831step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41831step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41831step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41831step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41831step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41831 raw41831Labels = mixedMoment B node4664 node4664Labels := by
  calc
    mixedMoment B raw41831 raw41831Labels = mixedMoment B raw41831step0 raw41831step0Labels := by
      have ha : raw41831step0 = (fun i j => raw41831 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41831step0 raw41831; decide +kernel
      have hl : raw41831step0Labels = raw41831Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41831 raw41831Labels permutation195 permutation7
    mixedMoment B raw41831step0 raw41831step0Labels = mixedMoment B raw41831step1 raw41831step1Labels := by
      have ha : raw41831step1 = -raw41831step0 := by apply Matrix.ext; change ∀ i j, raw41831step1 i j = -(raw41831step0 i j); unfold raw41831step1 raw41831step0; decide +kernel
      have hl : raw41831step1Labels = raw41831step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41831step1 raw41831step1Labels = mixedMoment B raw41831step2 raw41831step2Labels := by
      have ha : raw41831step2 = raw41831step1 := by apply Matrix.ext; unfold raw41831step2 raw41831step1; decide +kernel
      have hl : raw41831step1Labels = labelEmbedding6 ∘ raw41831step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41831step1 raw41831step1Labels raw41831step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4664 node4664Labels := by rfl

def raw41832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41832Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41832 raw41832Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw41832 raw41832Labels = mixedMoment B raw41832step0 raw41832step0Labels := by
      have ha : raw41832step0 = (fun i j => raw41832 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41832step0 raw41832; decide +kernel
      have hl : raw41832step0Labels = raw41832Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41832 raw41832Labels permutation180 permutation2
    mixedMoment B raw41832step0 raw41832step0Labels = mixedMoment B raw41832step1 raw41832step1Labels := by
      have ha : raw41832step1 = raw41832step0 := by apply Matrix.ext; unfold raw41832step1 raw41832step0; decide +kernel
      have hl : raw41832step0Labels = labelEmbedding1 ∘ raw41832step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41832step0 raw41832step0Labels raw41832step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2148 node2148Labels := by rfl

def raw41833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41833Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw41833step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41833step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41833step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41833 raw41833Labels = mixedMoment B node4666 node4666Labels := by
  calc
    mixedMoment B raw41833 raw41833Labels = mixedMoment B raw41833step0 raw41833step0Labels := by
      have ha : raw41833step0 = (fun i j => raw41833 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41833step0 raw41833; decide +kernel
      have hl : raw41833step0Labels = raw41833Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41833 raw41833Labels permutation194 permutation7
    mixedMoment B raw41833step0 raw41833step0Labels = mixedMoment B raw41833step1 raw41833step1Labels := by
      have ha : raw41833step1 = -raw41833step0 := by apply Matrix.ext; change ∀ i j, raw41833step1 i j = -(raw41833step0 i j); unfold raw41833step1 raw41833step0; decide +kernel
      have hl : raw41833step1Labels = raw41833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41833step1 raw41833step1Labels = mixedMoment B raw41833step2 raw41833step2Labels := by
      have ha : raw41833step2 = raw41833step1 := by apply Matrix.ext; unfold raw41833step2 raw41833step1; decide +kernel
      have hl : raw41833step1Labels = labelEmbedding6 ∘ raw41833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41833step1 raw41833step1Labels raw41833step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4666 node4666Labels := by rfl

def raw41834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw41834Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw41834step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw41834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41834step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![2, -3, 1]]
def raw41834step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41834step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw41834step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41834step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw41834step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41834step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw41834step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41834 raw41834Labels = mixedMoment B node1747 node1747Labels := by
  calc
    mixedMoment B raw41834 raw41834Labels = mixedMoment B raw41834step0 raw41834step0Labels := by
      have hz : ∀ j, raw41834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41834step0 = (fun i j => raw41834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41834step0 raw41834; decide +kernel
      have hl : raw41834step0Labels = raw41834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41834 raw41834Labels permutation434 hz
    mixedMoment B raw41834step0 raw41834step0Labels = mixedMoment B raw41834step1 raw41834step1Labels := by
      have hz : ∀ j, raw41834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41834step1 = (fun i j => raw41834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41834step1 raw41834step0; decide +kernel
      have hl : raw41834step1Labels = raw41834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41834step0 raw41834step0Labels permutation80 hz
    mixedMoment B raw41834step1 raw41834step1Labels = mixedMoment B raw41834step2 raw41834step2Labels := by
      have hz : ∀ j, raw41834step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41834step2 = (fun i j => raw41834step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41834step2 raw41834step1; decide +kernel
      have hl : raw41834step2Labels = raw41834step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41834step1 raw41834step1Labels permutation14 hz
    mixedMoment B raw41834step2 raw41834step2Labels = mixedMoment B raw41834step3 raw41834step3Labels := by
      have ha : raw41834step3 = (fun i j => raw41834step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41834step3 raw41834step2; decide +kernel
      have hl : raw41834step3Labels = raw41834step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41834step2 raw41834step2Labels permutation4 permutation4
    mixedMoment B raw41834step3 raw41834step3Labels = mixedMoment B raw41834step4 raw41834step4Labels := by
      have ha : raw41834step4 = -raw41834step3 := by apply Matrix.ext; change ∀ i j, raw41834step4 i j = -(raw41834step3 i j); unfold raw41834step4 raw41834step3; decide +kernel
      have hl : raw41834step4Labels = raw41834step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41834step4 raw41834step4Labels = mixedMoment B raw41834step5 raw41834step5Labels := by
      have ha : raw41834step5 = raw41834step4 := by apply Matrix.ext; unfold raw41834step5 raw41834step4; decide +kernel
      have hl : raw41834step4Labels = labelEmbedding1 ∘ raw41834step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41834step4 raw41834step4Labels raw41834step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1747 node1747Labels := by rfl

def raw41835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw41835Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw41835step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw41835step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41835step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![2, -3, 1]]
def raw41835step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41835step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw41835step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41835 raw41835Labels = mixedMoment B node4508 node4508Labels := by
  calc
    mixedMoment B raw41835 raw41835Labels = mixedMoment B raw41835step0 raw41835step0Labels := by
      have hz : ∀ j, raw41835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41835step0 = (fun i j => raw41835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41835step0 raw41835; decide +kernel
      have hl : raw41835step0Labels = raw41835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41835 raw41835Labels permutation434 hz
    mixedMoment B raw41835step0 raw41835step0Labels = mixedMoment B raw41835step1 raw41835step1Labels := by
      have hz : ∀ j, raw41835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41835step1 = (fun i j => raw41835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41835step1 raw41835step0; decide +kernel
      have hl : raw41835step1Labels = raw41835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41835step0 raw41835step0Labels permutation80 hz
    mixedMoment B raw41835step1 raw41835step1Labels = mixedMoment B raw41835step2 raw41835step2Labels := by
      have hz : ∀ j, raw41835step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41835step2 = (fun i j => raw41835step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41835step2 raw41835step1; decide +kernel
      have hl : raw41835step2Labels = raw41835step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41835step1 raw41835step1Labels permutation14 hz
    mixedMoment B raw41835step2 raw41835step2Labels = mixedMoment B raw41835step3 raw41835step3Labels := by
      have ha : raw41835step3 = (fun i j => raw41835step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41835step3 raw41835step2; decide +kernel
      have hl : raw41835step3Labels = raw41835step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41835step2 raw41835step2Labels permutation5 permutation6
    _ = mixedMoment B node4508 node4508Labels := by rfl

def raw41836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw41836Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw41836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw41836step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41836step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![2, 3, -5]]
def raw41836step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41836step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-3, 1, 2]]
def raw41836step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41836step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw41836step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41836step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw41836step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41836 raw41836Labels = mixedMoment B node1531 node1531Labels := by
  calc
    mixedMoment B raw41836 raw41836Labels = mixedMoment B raw41836step0 raw41836step0Labels := by
      have hz : ∀ j, raw41836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41836step0 = (fun i j => raw41836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41836step0 raw41836; decide +kernel
      have hl : raw41836step0Labels = raw41836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41836 raw41836Labels permutation434 hz
    mixedMoment B raw41836step0 raw41836step0Labels = mixedMoment B raw41836step1 raw41836step1Labels := by
      have hz : ∀ j, raw41836step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41836step1 = (fun i j => raw41836step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41836step1 raw41836step0; decide +kernel
      have hl : raw41836step1Labels = raw41836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41836step0 raw41836step0Labels permutation80 hz
    mixedMoment B raw41836step1 raw41836step1Labels = mixedMoment B raw41836step2 raw41836step2Labels := by
      have hz : ∀ j, raw41836step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41836step2 = (fun i j => raw41836step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41836step2 raw41836step1; decide +kernel
      have hl : raw41836step2Labels = raw41836step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41836step1 raw41836step1Labels permutation14 hz
    mixedMoment B raw41836step2 raw41836step2Labels = mixedMoment B raw41836step3 raw41836step3Labels := by
      have ha : raw41836step3 = (fun i j => raw41836step2 (permutation6 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41836step3 raw41836step2; decide +kernel
      have hl : raw41836step3Labels = raw41836step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41836step2 raw41836step2Labels permutation6 permutation4
    mixedMoment B raw41836step3 raw41836step3Labels = mixedMoment B raw41836step4 raw41836step4Labels := by
      have ha : raw41836step4 = -raw41836step3 := by apply Matrix.ext; change ∀ i j, raw41836step4 i j = -(raw41836step3 i j); unfold raw41836step4 raw41836step3; decide +kernel
      have hl : raw41836step4Labels = raw41836step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41836step4 raw41836step4Labels = mixedMoment B raw41836step5 raw41836step5Labels := by
      have ha : raw41836step5 = raw41836step4 := by apply Matrix.ext; unfold raw41836step5 raw41836step4; decide +kernel
      have hl : raw41836step4Labels = labelEmbedding1 ∘ raw41836step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41836step4 raw41836step4Labels raw41836step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1531 node1531Labels := by rfl

def raw41837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw41837Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw41837step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw41837step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41837step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![2, 3, -5]]
def raw41837step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41837step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw41837step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41837 raw41837Labels = mixedMoment B node4193 node4193Labels := by
  calc
    mixedMoment B raw41837 raw41837Labels = mixedMoment B raw41837step0 raw41837step0Labels := by
      have hz : ∀ j, raw41837 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41837step0 = (fun i j => raw41837 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41837step0 raw41837; decide +kernel
      have hl : raw41837step0Labels = raw41837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41837 raw41837Labels permutation434 hz
    mixedMoment B raw41837step0 raw41837step0Labels = mixedMoment B raw41837step1 raw41837step1Labels := by
      have hz : ∀ j, raw41837step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41837step1 = (fun i j => raw41837step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41837step1 raw41837step0; decide +kernel
      have hl : raw41837step1Labels = raw41837step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41837step0 raw41837step0Labels permutation80 hz
    mixedMoment B raw41837step1 raw41837step1Labels = mixedMoment B raw41837step2 raw41837step2Labels := by
      have hz : ∀ j, raw41837step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41837step2 = (fun i j => raw41837step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41837step2 raw41837step1; decide +kernel
      have hl : raw41837step2Labels = raw41837step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41837step1 raw41837step1Labels permutation14 hz
    mixedMoment B raw41837step2 raw41837step2Labels = mixedMoment B raw41837step3 raw41837step3Labels := by
      have ha : raw41837step3 = (fun i j => raw41837step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41837step3 raw41837step2; decide +kernel
      have hl : raw41837step3Labels = raw41837step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41837step2 raw41837step2Labels permutation7 permutation6
    _ = mixedMoment B node4193 node4193Labels := by rfl

def raw41838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw41838Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw41838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw41838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw41838step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41838step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41838step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41838step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41838 raw41838Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw41838 raw41838Labels = mixedMoment B raw41838step0 raw41838step0Labels := by
      have hz : ∀ j, raw41838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41838step0 = (fun i j => raw41838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41838step0 raw41838; decide +kernel
      have hl : raw41838step0Labels = raw41838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41838 raw41838Labels permutation346 hz
    mixedMoment B raw41838step0 raw41838step0Labels = mixedMoment B raw41838step1 raw41838step1Labels := by
      have hz : ∀ j, raw41838step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41838step1 = (fun i j => raw41838step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41838step1 raw41838step0; decide +kernel
      have hl : raw41838step1Labels = raw41838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41838step0 raw41838step0Labels permutation56 hz
    mixedMoment B raw41838step1 raw41838step1Labels = mixedMoment B raw41838step2 raw41838step2Labels := by
      have ha : raw41838step2 = (fun i j => raw41838step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41838step2 raw41838step1; decide +kernel
      have hl : raw41838step2Labels = raw41838step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41838step1 raw41838step1Labels permutation20 permutation4
    mixedMoment B raw41838step2 raw41838step2Labels = mixedMoment B raw41838step3 raw41838step3Labels := by
      have ha : raw41838step3 = -raw41838step2 := by apply Matrix.ext; change ∀ i j, raw41838step3 i j = -(raw41838step2 i j); unfold raw41838step3 raw41838step2; decide +kernel
      have hl : raw41838step3Labels = raw41838step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41838step3 raw41838step3Labels = mixedMoment B raw41838step4 raw41838step4Labels := by
      have ha : raw41838step4 = raw41838step3 := by apply Matrix.ext; unfold raw41838step4 raw41838step3; decide +kernel
      have hl : raw41838step3Labels = labelEmbedding1 ∘ raw41838step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41838step3 raw41838step3Labels raw41838step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

def raw41839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw41839Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw41839step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw41839step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw41839step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41839 raw41839Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw41839 raw41839Labels = mixedMoment B raw41839step0 raw41839step0Labels := by
      have hz : ∀ j, raw41839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41839step0 = (fun i j => raw41839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41839step0 raw41839; decide +kernel
      have hl : raw41839step0Labels = raw41839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41839 raw41839Labels permutation346 hz
    mixedMoment B raw41839step0 raw41839step0Labels = mixedMoment B raw41839step1 raw41839step1Labels := by
      have hz : ∀ j, raw41839step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41839step1 = (fun i j => raw41839step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41839step1 raw41839step0; decide +kernel
      have hl : raw41839step1Labels = raw41839step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41839step0 raw41839step0Labels permutation56 hz
    mixedMoment B raw41839step1 raw41839step1Labels = mixedMoment B raw41839step2 raw41839step2Labels := by
      have ha : raw41839step2 = (fun i j => raw41839step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41839step2 raw41839step1; decide +kernel
      have hl : raw41839step2Labels = raw41839step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41839step1 raw41839step1Labels permutation25 permutation6
    _ = mixedMoment B node4478 node4478Labels := by rfl

def raw41840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41840Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41840step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41840step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw41840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41840step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41840step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41840step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41840step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41840 raw41840Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw41840 raw41840Labels = mixedMoment B raw41840step0 raw41840step0Labels := by
      have hz : ∀ j, raw41840 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41840step0 = (fun i j => raw41840 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41840step0 raw41840; decide +kernel
      have hl : raw41840step0Labels = raw41840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41840 raw41840Labels permutation346 hz
    mixedMoment B raw41840step0 raw41840step0Labels = mixedMoment B raw41840step1 raw41840step1Labels := by
      have hz : ∀ j, raw41840step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41840step1 = (fun i j => raw41840step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41840step1 raw41840step0; decide +kernel
      have hl : raw41840step1Labels = raw41840step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41840step0 raw41840step0Labels permutation56 hz
    mixedMoment B raw41840step1 raw41840step1Labels = mixedMoment B raw41840step2 raw41840step2Labels := by
      have ha : raw41840step2 = (fun i j => raw41840step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41840step2 raw41840step1; decide +kernel
      have hl : raw41840step2Labels = raw41840step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41840step1 raw41840step1Labels permutation26 permutation4
    mixedMoment B raw41840step2 raw41840step2Labels = mixedMoment B raw41840step3 raw41840step3Labels := by
      have ha : raw41840step3 = -raw41840step2 := by apply Matrix.ext; change ∀ i j, raw41840step3 i j = -(raw41840step2 i j); unfold raw41840step3 raw41840step2; decide +kernel
      have hl : raw41840step3Labels = raw41840step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41840step3 raw41840step3Labels = mixedMoment B raw41840step4 raw41840step4Labels := by
      have ha : raw41840step4 = raw41840step3 := by apply Matrix.ext; unfold raw41840step4 raw41840step3; decide +kernel
      have hl : raw41840step3Labels = labelEmbedding1 ∘ raw41840step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41840step3 raw41840step3Labels raw41840step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1530 node1530Labels := by rfl

def raw41841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41841Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41841step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41841step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41841step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41841 raw41841Labels = mixedMoment B node4184 node4184Labels := by
  calc
    mixedMoment B raw41841 raw41841Labels = mixedMoment B raw41841step0 raw41841step0Labels := by
      have hz : ∀ j, raw41841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41841step0 = (fun i j => raw41841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41841step0 raw41841; decide +kernel
      have hl : raw41841step0Labels = raw41841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41841 raw41841Labels permutation346 hz
    mixedMoment B raw41841step0 raw41841step0Labels = mixedMoment B raw41841step1 raw41841step1Labels := by
      have hz : ∀ j, raw41841step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41841step1 = (fun i j => raw41841step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41841step1 raw41841step0; decide +kernel
      have hl : raw41841step1Labels = raw41841step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41841step0 raw41841step0Labels permutation56 hz
    mixedMoment B raw41841step1 raw41841step1Labels = mixedMoment B raw41841step2 raw41841step2Labels := by
      have ha : raw41841step2 = (fun i j => raw41841step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41841step2 raw41841step1; decide +kernel
      have hl : raw41841step2Labels = raw41841step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41841step1 raw41841step1Labels permutation29 permutation6
    _ = mixedMoment B node4184 node4184Labels := by rfl

def raw41842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41842Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41842step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw41842step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41842step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41842step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41842step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41842step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41842 raw41842Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw41842 raw41842Labels = mixedMoment B raw41842step0 raw41842step0Labels := by
      have hz : ∀ j, raw41842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41842step0 = (fun i j => raw41842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41842step0 raw41842; decide +kernel
      have hl : raw41842step0Labels = raw41842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41842 raw41842Labels permutation346 hz
    mixedMoment B raw41842step0 raw41842step0Labels = mixedMoment B raw41842step1 raw41842step1Labels := by
      have hz : ∀ j, raw41842step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41842step1 = (fun i j => raw41842step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41842step1 raw41842step0; decide +kernel
      have hl : raw41842step1Labels = raw41842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41842step0 raw41842step0Labels permutation56 hz
    mixedMoment B raw41842step1 raw41842step1Labels = mixedMoment B raw41842step2 raw41842step2Labels := by
      have ha : raw41842step2 = (fun i j => raw41842step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41842step2 raw41842step1; decide +kernel
      have hl : raw41842step2Labels = raw41842step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41842step1 raw41842step1Labels permutation27 permutation4
    mixedMoment B raw41842step2 raw41842step2Labels = mixedMoment B raw41842step3 raw41842step3Labels := by
      have ha : raw41842step3 = -raw41842step2 := by apply Matrix.ext; change ∀ i j, raw41842step3 i j = -(raw41842step2 i j); unfold raw41842step3 raw41842step2; decide +kernel
      have hl : raw41842step3Labels = raw41842step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41842step3 raw41842step3Labels = mixedMoment B raw41842step4 raw41842step4Labels := by
      have ha : raw41842step4 = raw41842step3 := by apply Matrix.ext; unfold raw41842step4 raw41842step3; decide +kernel
      have hl : raw41842step3Labels = labelEmbedding1 ∘ raw41842step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41842step3 raw41842step3Labels raw41842step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1529 node1529Labels := by rfl

def raw41843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41843Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41843step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41843step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41843 raw41843Labels = mixedMoment B node4162 node4162Labels := by
  calc
    mixedMoment B raw41843 raw41843Labels = mixedMoment B raw41843step0 raw41843step0Labels := by
      have hz : ∀ j, raw41843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41843step0 = (fun i j => raw41843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41843step0 raw41843; decide +kernel
      have hl : raw41843step0Labels = raw41843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41843 raw41843Labels permutation346 hz
    mixedMoment B raw41843step0 raw41843step0Labels = mixedMoment B raw41843step1 raw41843step1Labels := by
      have hz : ∀ j, raw41843step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41843step1 = (fun i j => raw41843step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41843step1 raw41843step0; decide +kernel
      have hl : raw41843step1Labels = raw41843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41843step0 raw41843step0Labels permutation56 hz
    mixedMoment B raw41843step1 raw41843step1Labels = mixedMoment B raw41843step2 raw41843step2Labels := by
      have ha : raw41843step2 = (fun i j => raw41843step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41843step2 raw41843step1; decide +kernel
      have hl : raw41843step2Labels = raw41843step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41843step1 raw41843step1Labels permutation31 permutation6
    _ = mixedMoment B node4162 node4162Labels := by rfl

def raw41844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw41844Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw41844step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw41844step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw41844step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41844step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw41844step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41844step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw41844step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41844 raw41844Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw41844 raw41844Labels = mixedMoment B raw41844step0 raw41844step0Labels := by
      have hz : ∀ j, raw41844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41844step0 = (fun i j => raw41844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41844step0 raw41844; decide +kernel
      have hl : raw41844step0Labels = raw41844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41844 raw41844Labels permutation346 hz
    mixedMoment B raw41844step0 raw41844step0Labels = mixedMoment B raw41844step1 raw41844step1Labels := by
      have hz : ∀ j, raw41844step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41844step1 = (fun i j => raw41844step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41844step1 raw41844step0; decide +kernel
      have hl : raw41844step1Labels = raw41844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41844step0 raw41844step0Labels permutation56 hz
    mixedMoment B raw41844step1 raw41844step1Labels = mixedMoment B raw41844step2 raw41844step2Labels := by
      have ha : raw41844step2 = (fun i j => raw41844step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41844step2 raw41844step1; decide +kernel
      have hl : raw41844step2Labels = raw41844step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41844step1 raw41844step1Labels permutation16 permutation4
    mixedMoment B raw41844step2 raw41844step2Labels = mixedMoment B raw41844step3 raw41844step3Labels := by
      have ha : raw41844step3 = -raw41844step2 := by apply Matrix.ext; change ∀ i j, raw41844step3 i j = -(raw41844step2 i j); unfold raw41844step3 raw41844step2; decide +kernel
      have hl : raw41844step3Labels = raw41844step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41844step3 raw41844step3Labels = mixedMoment B raw41844step4 raw41844step4Labels := by
      have ha : raw41844step4 = raw41844step3 := by apply Matrix.ext; unfold raw41844step4 raw41844step3; decide +kernel
      have hl : raw41844step3Labels = labelEmbedding1 ∘ raw41844step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41844step3 raw41844step3Labels raw41844step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1687 node1687Labels := by rfl

def raw41845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw41845Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw41845step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41845step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw41845step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41845step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw41845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41845 raw41845Labels = mixedMoment B node4362 node4362Labels := by
  calc
    mixedMoment B raw41845 raw41845Labels = mixedMoment B raw41845step0 raw41845step0Labels := by
      have hz : ∀ j, raw41845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41845step0 = (fun i j => raw41845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41845step0 raw41845; decide +kernel
      have hl : raw41845step0Labels = raw41845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41845 raw41845Labels permutation346 hz
    mixedMoment B raw41845step0 raw41845step0Labels = mixedMoment B raw41845step1 raw41845step1Labels := by
      have hz : ∀ j, raw41845step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41845step1 = (fun i j => raw41845step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41845step1 raw41845step0; decide +kernel
      have hl : raw41845step1Labels = raw41845step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41845step0 raw41845step0Labels permutation56 hz
    mixedMoment B raw41845step1 raw41845step1Labels = mixedMoment B raw41845step2 raw41845step2Labels := by
      have ha : raw41845step2 = (fun i j => raw41845step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41845step2 raw41845step1; decide +kernel
      have hl : raw41845step2Labels = raw41845step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41845step1 raw41845step1Labels permutation17 permutation6
    _ = mixedMoment B node4362 node4362Labels := by rfl

def raw41846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw41846Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw41846step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw41846step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw41846step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41846step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41846step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41846step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41846step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41846 raw41846Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw41846 raw41846Labels = mixedMoment B raw41846step0 raw41846step0Labels := by
      have hz : ∀ j, raw41846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41846step0 = (fun i j => raw41846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41846step0 raw41846; decide +kernel
      have hl : raw41846step0Labels = raw41846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41846 raw41846Labels permutation346 hz
    mixedMoment B raw41846step0 raw41846step0Labels = mixedMoment B raw41846step1 raw41846step1Labels := by
      have hz : ∀ j, raw41846step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41846step1 = (fun i j => raw41846step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41846step1 raw41846step0; decide +kernel
      have hl : raw41846step1Labels = raw41846step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41846step0 raw41846step0Labels permutation56 hz
    mixedMoment B raw41846step1 raw41846step1Labels = mixedMoment B raw41846step2 raw41846step2Labels := by
      have ha : raw41846step2 = (fun i j => raw41846step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41846step2 raw41846step1; decide +kernel
      have hl : raw41846step2Labels = raw41846step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41846step1 raw41846step1Labels permutation14 permutation4
    mixedMoment B raw41846step2 raw41846step2Labels = mixedMoment B raw41846step3 raw41846step3Labels := by
      have ha : raw41846step3 = -raw41846step2 := by apply Matrix.ext; change ∀ i j, raw41846step3 i j = -(raw41846step2 i j); unfold raw41846step3 raw41846step2; decide +kernel
      have hl : raw41846step3Labels = raw41846step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41846step3 raw41846step3Labels = mixedMoment B raw41846step4 raw41846step4Labels := by
      have ha : raw41846step4 = raw41846step3 := by apply Matrix.ext; unfold raw41846step4 raw41846step3; decide +kernel
      have hl : raw41846step3Labels = labelEmbedding1 ∘ raw41846step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41846step3 raw41846step3Labels raw41846step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

def raw41847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw41847Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw41847step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw41847step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41847step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41847 raw41847Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw41847 raw41847Labels = mixedMoment B raw41847step0 raw41847step0Labels := by
      have hz : ∀ j, raw41847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41847step0 = (fun i j => raw41847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41847step0 raw41847; decide +kernel
      have hl : raw41847step0Labels = raw41847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41847 raw41847Labels permutation346 hz
    mixedMoment B raw41847step0 raw41847step0Labels = mixedMoment B raw41847step1 raw41847step1Labels := by
      have hz : ∀ j, raw41847step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41847step1 = (fun i j => raw41847step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41847step1 raw41847step0; decide +kernel
      have hl : raw41847step1Labels = raw41847step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41847step0 raw41847step0Labels permutation56 hz
    mixedMoment B raw41847step1 raw41847step1Labels = mixedMoment B raw41847step2 raw41847step2Labels := by
      have ha : raw41847step2 = (fun i j => raw41847step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41847step2 raw41847step1; decide +kernel
      have hl : raw41847step2Labels = raw41847step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41847step1 raw41847step1Labels permutation17 permutation6
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw41848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw41848Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw41848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw41848step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw41848step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41848step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw41848step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41848 raw41848Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw41848 raw41848Labels = mixedMoment B raw41848step0 raw41848step0Labels := by
      have hz : ∀ j, raw41848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41848step0 = (fun i j => raw41848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41848step0 raw41848; decide +kernel
      have hl : raw41848step0Labels = raw41848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41848 raw41848Labels permutation346 hz
    mixedMoment B raw41848step0 raw41848step0Labels = mixedMoment B raw41848step1 raw41848step1Labels := by
      have hz : ∀ j, raw41848step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41848step1 = (fun i j => raw41848step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41848step1 raw41848step0; decide +kernel
      have hl : raw41848step1Labels = raw41848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41848step0 raw41848step0Labels permutation56 hz
    mixedMoment B raw41848step1 raw41848step1Labels = mixedMoment B raw41848step2 raw41848step2Labels := by
      have ha : raw41848step2 = (fun i j => raw41848step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41848step2 raw41848step1; decide +kernel
      have hl : raw41848step2Labels = raw41848step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41848step1 raw41848step1Labels permutation13 permutation2
    mixedMoment B raw41848step2 raw41848step2Labels = mixedMoment B raw41848step3 raw41848step3Labels := by
      have ha : raw41848step3 = raw41848step2 := by apply Matrix.ext; unfold raw41848step3 raw41848step2; decide +kernel
      have hl : raw41848step2Labels = labelEmbedding1 ∘ raw41848step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41848step2 raw41848step2Labels raw41848step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2286 node2286Labels := by rfl

def raw41849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw41849Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw41849step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw41849step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41849step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41849step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41849step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41849step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41849step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41849step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41849 raw41849Labels = mixedMoment B node4705 node4705Labels := by
  calc
    mixedMoment B raw41849 raw41849Labels = mixedMoment B raw41849step0 raw41849step0Labels := by
      have hz : ∀ j, raw41849 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41849step0 = (fun i j => raw41849 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41849step0 raw41849; decide +kernel
      have hl : raw41849step0Labels = raw41849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41849 raw41849Labels permutation346 hz
    mixedMoment B raw41849step0 raw41849step0Labels = mixedMoment B raw41849step1 raw41849step1Labels := by
      have hz : ∀ j, raw41849step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41849step1 = (fun i j => raw41849step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41849step1 raw41849step0; decide +kernel
      have hl : raw41849step1Labels = raw41849step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41849step0 raw41849step0Labels permutation56 hz
    mixedMoment B raw41849step1 raw41849step1Labels = mixedMoment B raw41849step2 raw41849step2Labels := by
      have ha : raw41849step2 = (fun i j => raw41849step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41849step2 raw41849step1; decide +kernel
      have hl : raw41849step2Labels = raw41849step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41849step1 raw41849step1Labels permutation13 permutation7
    mixedMoment B raw41849step2 raw41849step2Labels = mixedMoment B raw41849step3 raw41849step3Labels := by
      have ha : raw41849step3 = -raw41849step2 := by apply Matrix.ext; change ∀ i j, raw41849step3 i j = -(raw41849step2 i j); unfold raw41849step3 raw41849step2; decide +kernel
      have hl : raw41849step3Labels = raw41849step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41849step3 raw41849step3Labels = mixedMoment B raw41849step4 raw41849step4Labels := by
      have ha : raw41849step4 = raw41849step3 := by apply Matrix.ext; unfold raw41849step4 raw41849step3; decide +kernel
      have hl : raw41849step3Labels = labelEmbedding6 ∘ raw41849step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41849step3 raw41849step3Labels raw41849step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4705 node4705Labels := by rfl

def raw41850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41850Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41850step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41850step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41850step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41850step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41850 raw41850Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw41850 raw41850Labels = mixedMoment B raw41850step0 raw41850step0Labels := by
      have hz : ∀ j, raw41850 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41850step0 = (fun i j => raw41850 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41850step0 raw41850; decide +kernel
      have hl : raw41850step0Labels = raw41850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41850 raw41850Labels permutation265 hz
    mixedMoment B raw41850step0 raw41850step0Labels = mixedMoment B raw41850step1 raw41850step1Labels := by
      have ha : raw41850step1 = (fun i j => raw41850step0 (permutation132 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41850step1 raw41850step0; decide +kernel
      have hl : raw41850step1Labels = raw41850step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41850step0 raw41850step0Labels permutation132 permutation4
    mixedMoment B raw41850step1 raw41850step1Labels = mixedMoment B raw41850step2 raw41850step2Labels := by
      have ha : raw41850step2 = -raw41850step1 := by apply Matrix.ext; change ∀ i j, raw41850step2 i j = -(raw41850step1 i j); unfold raw41850step2 raw41850step1; decide +kernel
      have hl : raw41850step2Labels = raw41850step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41850step2 raw41850step2Labels = mixedMoment B raw41850step3 raw41850step3Labels := by
      have ha : raw41850step3 = raw41850step2 := by apply Matrix.ext; unfold raw41850step3 raw41850step2; decide +kernel
      have hl : raw41850step2Labels = labelEmbedding1 ∘ raw41850step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41850step2 raw41850step2Labels raw41850step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1528 node1528Labels := by rfl

def raw41851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41851Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41851step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41851 raw41851Labels = mixedMoment B node4157 node4157Labels := by
  calc
    mixedMoment B raw41851 raw41851Labels = mixedMoment B raw41851step0 raw41851step0Labels := by
      have hz : ∀ j, raw41851 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41851step0 = (fun i j => raw41851 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41851step0 raw41851; decide +kernel
      have hl : raw41851step0Labels = raw41851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41851 raw41851Labels permutation265 hz
    mixedMoment B raw41851step0 raw41851step0Labels = mixedMoment B raw41851step1 raw41851step1Labels := by
      have ha : raw41851step1 = (fun i j => raw41851step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41851step1 raw41851step0; decide +kernel
      have hl : raw41851step1Labels = raw41851step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41851step0 raw41851step0Labels permutation149 permutation6
    _ = mixedMoment B node4157 node4157Labels := by rfl

def raw41852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41852Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41852step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw41852step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41852step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41852step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41852step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41852 raw41852Labels = mixedMoment B node1686 node1686Labels := by
  calc
    mixedMoment B raw41852 raw41852Labels = mixedMoment B raw41852step0 raw41852step0Labels := by
      have hz : ∀ j, raw41852 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41852step0 = (fun i j => raw41852 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41852step0 raw41852; decide +kernel
      have hl : raw41852step0Labels = raw41852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41852 raw41852Labels permutation265 hz
    mixedMoment B raw41852step0 raw41852step0Labels = mixedMoment B raw41852step1 raw41852step1Labels := by
      have ha : raw41852step1 = (fun i j => raw41852step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41852step1 raw41852step0; decide +kernel
      have hl : raw41852step1Labels = raw41852step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41852step0 raw41852step0Labels permutation92 permutation4
    mixedMoment B raw41852step1 raw41852step1Labels = mixedMoment B raw41852step2 raw41852step2Labels := by
      have ha : raw41852step2 = -raw41852step1 := by apply Matrix.ext; change ∀ i j, raw41852step2 i j = -(raw41852step1 i j); unfold raw41852step2 raw41852step1; decide +kernel
      have hl : raw41852step2Labels = raw41852step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41852step2 raw41852step2Labels = mixedMoment B raw41852step3 raw41852step3Labels := by
      have ha : raw41852step3 = raw41852step2 := by apply Matrix.ext; unfold raw41852step3 raw41852step2; decide +kernel
      have hl : raw41852step2Labels = labelEmbedding1 ∘ raw41852step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41852step2 raw41852step2Labels raw41852step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1686 node1686Labels := by rfl

def raw41853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41853Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41853step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41853 raw41853Labels = mixedMoment B node4353 node4353Labels := by
  calc
    mixedMoment B raw41853 raw41853Labels = mixedMoment B raw41853step0 raw41853step0Labels := by
      have hz : ∀ j, raw41853 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41853step0 = (fun i j => raw41853 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41853step0 raw41853; decide +kernel
      have hl : raw41853step0Labels = raw41853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41853 raw41853Labels permutation265 hz
    mixedMoment B raw41853step0 raw41853step0Labels = mixedMoment B raw41853step1 raw41853step1Labels := by
      have ha : raw41853step1 = (fun i j => raw41853step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41853step1 raw41853step0; decide +kernel
      have hl : raw41853step1Labels = raw41853step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41853step0 raw41853step0Labels permutation95 permutation6
    _ = mixedMoment B node4353 node4353Labels := by rfl

def raw41854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41854Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41854step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41854step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41854step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41854step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41854 raw41854Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw41854 raw41854Labels = mixedMoment B raw41854step0 raw41854step0Labels := by
      have hz : ∀ j, raw41854 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41854step0 = (fun i j => raw41854 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41854step0 raw41854; decide +kernel
      have hl : raw41854step0Labels = raw41854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41854 raw41854Labels permutation265 hz
    mixedMoment B raw41854step0 raw41854step0Labels = mixedMoment B raw41854step1 raw41854step1Labels := by
      have ha : raw41854step1 = (fun i j => raw41854step0 (permutation83 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41854step1 raw41854step0; decide +kernel
      have hl : raw41854step1Labels = raw41854step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41854step0 raw41854step0Labels permutation83 permutation4
    mixedMoment B raw41854step1 raw41854step1Labels = mixedMoment B raw41854step2 raw41854step2Labels := by
      have ha : raw41854step2 = -raw41854step1 := by apply Matrix.ext; change ∀ i j, raw41854step2 i j = -(raw41854step1 i j); unfold raw41854step2 raw41854step1; decide +kernel
      have hl : raw41854step2Labels = raw41854step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41854step2 raw41854step2Labels = mixedMoment B raw41854step3 raw41854step3Labels := by
      have ha : raw41854step3 = raw41854step2 := by apply Matrix.ext; unfold raw41854step3 raw41854step2; decide +kernel
      have hl : raw41854step2Labels = labelEmbedding1 ∘ raw41854step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41854step2 raw41854step2Labels raw41854step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw41855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41855Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41855step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41855 raw41855Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw41855 raw41855Labels = mixedMoment B raw41855step0 raw41855step0Labels := by
      have hz : ∀ j, raw41855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41855step0 = (fun i j => raw41855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41855step0 raw41855; decide +kernel
      have hl : raw41855step0Labels = raw41855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41855 raw41855Labels permutation265 hz
    mixedMoment B raw41855step0 raw41855step0Labels = mixedMoment B raw41855step1 raw41855step1Labels := by
      have ha : raw41855step1 = (fun i j => raw41855step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41855step1 raw41855step0; decide +kernel
      have hl : raw41855step1Labels = raw41855step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41855step0 raw41855step0Labels permutation97 permutation6
    _ = mixedMoment B node4442 node4442Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
