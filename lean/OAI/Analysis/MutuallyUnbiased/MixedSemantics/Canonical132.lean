import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16896 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16896step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16896step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16896step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16896 raw16896Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw16896 raw16896Labels = mixedMoment B raw16896step0 raw16896step0Labels := by
      have hz : ∀ j, raw16896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16896step0 = (fun i j => raw16896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16896step0 raw16896; decide +kernel
      have hl : raw16896step0Labels = raw16896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16896 raw16896Labels permutation434 hz
    mixedMoment B raw16896step0 raw16896step0Labels = mixedMoment B raw16896step1 raw16896step1Labels := by
      have ha : raw16896step1 = (fun i j => raw16896step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16896step1 raw16896step0; decide +kernel
      have hl : raw16896step1Labels = raw16896step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16896step0 raw16896step0Labels permutation151 permutation7
    mixedMoment B raw16896step1 raw16896step1Labels = mixedMoment B raw16896step2 raw16896step2Labels := by
      have ha : raw16896step2 = -raw16896step1 := by apply Matrix.ext; change ∀ i j, raw16896step2 i j = -(raw16896step1 i j); unfold raw16896step2 raw16896step1; decide +kernel
      have hl : raw16896step2Labels = raw16896step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16896step2 raw16896step2Labels = mixedMoment B raw16896step3 raw16896step3Labels := by
      have ha : raw16896step3 = raw16896step2 := by apply Matrix.ext; unfold raw16896step3 raw16896step2; decide +kernel
      have hl : raw16896step2Labels = labelEmbedding1 ∘ raw16896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16896step2 raw16896step2Labels raw16896step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw16897 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16897step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16897 raw16897Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw16897 raw16897Labels = mixedMoment B raw16897step0 raw16897step0Labels := by
      have ha : raw16897step0 = (fun i j => raw16897 (permutation398 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16897step0 raw16897; decide +kernel
      have hl : raw16897step0Labels = raw16897Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16897 raw16897Labels permutation398 permutation5
    mixedMoment B raw16897step0 raw16897step0Labels = mixedMoment B raw16897step1 raw16897step1Labels := by
      have ha : raw16897step1 = raw16897step0 := by apply Matrix.ext; unfold raw16897step1 raw16897step0; decide +kernel
      have hl : raw16897step0Labels = labelEmbedding1 ∘ raw16897step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16897step0 raw16897step0Labels raw16897step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3783 node3783Labels := by rfl

def raw16898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16898 raw16898Labels = mixedMoment B node2613 node2613Labels := by
  calc
    mixedMoment B raw16898 raw16898Labels = mixedMoment B raw16898step0 raw16898step0Labels := by
      have ha : raw16898step0 = (fun i j => raw16898 (permutation282 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16898step0 raw16898; decide +kernel
      have hl : raw16898step0Labels = raw16898Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16898 raw16898Labels permutation282 permutation5
    mixedMoment B raw16898step0 raw16898step0Labels = mixedMoment B raw16898step1 raw16898step1Labels := by
      have ha : raw16898step1 = -raw16898step0 := by apply Matrix.ext; change ∀ i j, raw16898step1 i j = -(raw16898step0 i j); unfold raw16898step1 raw16898step0; decide +kernel
      have hl : raw16898step1Labels = raw16898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16898step1 raw16898step1Labels = mixedMoment B raw16898step2 raw16898step2Labels := by
      have ha : raw16898step2 = raw16898step1 := by apply Matrix.ext; unfold raw16898step2 raw16898step1; decide +kernel
      have hl : raw16898step1Labels = labelEmbedding1 ∘ raw16898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16898step1 raw16898step1Labels raw16898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2613 node2613Labels := by rfl

def raw16899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16899Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16899step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16899step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16899 raw16899Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw16899 raw16899Labels = mixedMoment B raw16899step0 raw16899step0Labels := by
      have hz : ∀ j, raw16899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16899step0 = (fun i j => raw16899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16899step0 raw16899; decide +kernel
      have hl : raw16899step0Labels = raw16899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16899 raw16899Labels permutation434 hz
    mixedMoment B raw16899step0 raw16899step0Labels = mixedMoment B raw16899step1 raw16899step1Labels := by
      have ha : raw16899step1 = (fun i j => raw16899step0 (permutation102 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16899step1 raw16899step0; decide +kernel
      have hl : raw16899step1Labels = raw16899step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16899step0 raw16899step0Labels permutation102 permutation5
    mixedMoment B raw16899step1 raw16899step1Labels = mixedMoment B raw16899step2 raw16899step2Labels := by
      have ha : raw16899step2 = raw16899step1 := by apply Matrix.ext; unfold raw16899step2 raw16899step1; decide +kernel
      have hl : raw16899step1Labels = labelEmbedding1 ∘ raw16899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16899step1 raw16899step1Labels raw16899step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw16900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16900Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16900step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16900 raw16900Labels = mixedMoment B node3785 node3785Labels := by
  calc
    mixedMoment B raw16900 raw16900Labels = mixedMoment B raw16900step0 raw16900step0Labels := by
      have ha : raw16900step0 = (fun i j => raw16900 (permutation396 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16900step0 raw16900; decide +kernel
      have hl : raw16900step0Labels = raw16900Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16900 raw16900Labels permutation396 permutation5
    mixedMoment B raw16900step0 raw16900step0Labels = mixedMoment B raw16900step1 raw16900step1Labels := by
      have ha : raw16900step1 = raw16900step0 := by apply Matrix.ext; unfold raw16900step1 raw16900step0; decide +kernel
      have hl : raw16900step0Labels = labelEmbedding1 ∘ raw16900step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16900step0 raw16900step0Labels raw16900step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3785 node3785Labels := by rfl

def raw16901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16901Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16901step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16901 raw16901Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw16901 raw16901Labels = mixedMoment B raw16901step0 raw16901step0Labels := by
      have ha : raw16901step0 = (fun i j => raw16901 (permutation393 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16901step0 raw16901; decide +kernel
      have hl : raw16901step0Labels = raw16901Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16901 raw16901Labels permutation393 permutation5
    mixedMoment B raw16901step0 raw16901step0Labels = mixedMoment B raw16901step1 raw16901step1Labels := by
      have ha : raw16901step1 = raw16901step0 := by apply Matrix.ext; unfold raw16901step1 raw16901step0; decide +kernel
      have hl : raw16901step0Labels = labelEmbedding1 ∘ raw16901step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16901step0 raw16901step0Labels raw16901step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3802 node3802Labels := by rfl

def raw16902 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16902Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16902step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16902 raw16902Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw16902 raw16902Labels = mixedMoment B raw16902step0 raw16902step0Labels := by
      have ha : raw16902step0 = (fun i j => raw16902 (permutation483 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16902step0 raw16902; decide +kernel
      have hl : raw16902step0Labels = raw16902Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16902 raw16902Labels permutation483 permutation5
    mixedMoment B raw16902step0 raw16902step0Labels = mixedMoment B raw16902step1 raw16902step1Labels := by
      have ha : raw16902step1 = raw16902step0 := by apply Matrix.ext; unfold raw16902step1 raw16902step0; decide +kernel
      have hl : raw16902step0Labels = labelEmbedding1 ∘ raw16902step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16902step0 raw16902step0Labels raw16902step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3783 node3783Labels := by rfl

def raw16903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16903Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16903step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16903step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16903step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16903 raw16903Labels = mixedMoment B node2613 node2613Labels := by
  calc
    mixedMoment B raw16903 raw16903Labels = mixedMoment B raw16903step0 raw16903step0Labels := by
      have ha : raw16903step0 = (fun i j => raw16903 (permutation281 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16903step0 raw16903; decide +kernel
      have hl : raw16903step0Labels = raw16903Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16903 raw16903Labels permutation281 permutation5
    mixedMoment B raw16903step0 raw16903step0Labels = mixedMoment B raw16903step1 raw16903step1Labels := by
      have ha : raw16903step1 = -raw16903step0 := by apply Matrix.ext; change ∀ i j, raw16903step1 i j = -(raw16903step0 i j); unfold raw16903step1 raw16903step0; decide +kernel
      have hl : raw16903step1Labels = raw16903step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16903step1 raw16903step1Labels = mixedMoment B raw16903step2 raw16903step2Labels := by
      have ha : raw16903step2 = raw16903step1 := by apply Matrix.ext; unfold raw16903step2 raw16903step1; decide +kernel
      have hl : raw16903step1Labels = labelEmbedding1 ∘ raw16903step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16903step1 raw16903step1Labels raw16903step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2613 node2613Labels := by rfl

def raw16904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16904Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16904step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16904step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16904 raw16904Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw16904 raw16904Labels = mixedMoment B raw16904step0 raw16904step0Labels := by
      have hz : ∀ j, raw16904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16904step0 = (fun i j => raw16904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16904step0 raw16904; decide +kernel
      have hl : raw16904step0Labels = raw16904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16904 raw16904Labels permutation346 hz
    mixedMoment B raw16904step0 raw16904step0Labels = mixedMoment B raw16904step1 raw16904step1Labels := by
      have ha : raw16904step1 = (fun i j => raw16904step0 (permutation102 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16904step1 raw16904step0; decide +kernel
      have hl : raw16904step1Labels = raw16904step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16904step0 raw16904step0Labels permutation102 permutation5
    mixedMoment B raw16904step1 raw16904step1Labels = mixedMoment B raw16904step2 raw16904step2Labels := by
      have ha : raw16904step2 = raw16904step1 := by apply Matrix.ext; unfold raw16904step2 raw16904step1; decide +kernel
      have hl : raw16904step1Labels = labelEmbedding1 ∘ raw16904step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16904step1 raw16904step1Labels raw16904step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw16905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16905Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16905step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16905 raw16905Labels = mixedMoment B node3785 node3785Labels := by
  calc
    mixedMoment B raw16905 raw16905Labels = mixedMoment B raw16905step0 raw16905step0Labels := by
      have ha : raw16905step0 = (fun i j => raw16905 (permutation481 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16905step0 raw16905; decide +kernel
      have hl : raw16905step0Labels = raw16905Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16905 raw16905Labels permutation481 permutation5
    mixedMoment B raw16905step0 raw16905step0Labels = mixedMoment B raw16905step1 raw16905step1Labels := by
      have ha : raw16905step1 = raw16905step0 := by apply Matrix.ext; unfold raw16905step1 raw16905step0; decide +kernel
      have hl : raw16905step0Labels = labelEmbedding1 ∘ raw16905step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16905step0 raw16905step0Labels raw16905step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3785 node3785Labels := by rfl

def raw16906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16906Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16906step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16906 raw16906Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw16906 raw16906Labels = mixedMoment B raw16906step0 raw16906step0Labels := by
      have ha : raw16906step0 = (fun i j => raw16906 (permutation479 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16906step0 raw16906; decide +kernel
      have hl : raw16906step0Labels = raw16906Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16906 raw16906Labels permutation479 permutation5
    mixedMoment B raw16906step0 raw16906step0Labels = mixedMoment B raw16906step1 raw16906step1Labels := by
      have ha : raw16906step1 = raw16906step0 := by apply Matrix.ext; unfold raw16906step1 raw16906step0; decide +kernel
      have hl : raw16906step0Labels = labelEmbedding1 ∘ raw16906step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16906step0 raw16906step0Labels raw16906step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3802 node3802Labels := by rfl

def raw16907 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16907Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16907step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16907step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16907 raw16907Labels = mixedMoment B node3938 node3938Labels := by
  calc
    mixedMoment B raw16907 raw16907Labels = mixedMoment B raw16907step0 raw16907step0Labels := by
      have ha : raw16907step0 = (fun i j => raw16907 (permutation287 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16907step0 raw16907; decide +kernel
      have hl : raw16907step0Labels = raw16907Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16907 raw16907Labels permutation287 permutation5
    mixedMoment B raw16907step0 raw16907step0Labels = mixedMoment B raw16907step1 raw16907step1Labels := by
      have ha : raw16907step1 = -raw16907step0 := by apply Matrix.ext; change ∀ i j, raw16907step1 i j = -(raw16907step0 i j); unfold raw16907step1 raw16907step0; decide +kernel
      have hl : raw16907step1Labels = raw16907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16907step1 raw16907step1Labels = mixedMoment B raw16907step2 raw16907step2Labels := by
      have ha : raw16907step2 = raw16907step1 := by apply Matrix.ext; unfold raw16907step2 raw16907step1; decide +kernel
      have hl : raw16907step1Labels = labelEmbedding1 ∘ raw16907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16907step1 raw16907step1Labels raw16907step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3938 node3938Labels := by rfl

def raw16908 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16908Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16908step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16908step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16908step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16908 raw16908Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw16908 raw16908Labels = mixedMoment B raw16908step0 raw16908step0Labels := by
      have ha : raw16908step0 = (fun i j => raw16908 (permutation287 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16908step0 raw16908; decide +kernel
      have hl : raw16908step0Labels = raw16908Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16908 raw16908Labels permutation287 permutation5
    mixedMoment B raw16908step0 raw16908step0Labels = mixedMoment B raw16908step1 raw16908step1Labels := by
      have ha : raw16908step1 = -raw16908step0 := by apply Matrix.ext; change ∀ i j, raw16908step1 i j = -(raw16908step0 i j); unfold raw16908step1 raw16908step0; decide +kernel
      have hl : raw16908step1Labels = raw16908step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16908step1 raw16908step1Labels = mixedMoment B raw16908step2 raw16908step2Labels := by
      have ha : raw16908step2 = raw16908step1 := by apply Matrix.ext; unfold raw16908step2 raw16908step1; decide +kernel
      have hl : raw16908step1Labels = labelEmbedding1 ∘ raw16908step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16908step1 raw16908step1Labels raw16908step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2631 node2631Labels := by rfl

def raw16909 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16909Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16909step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16909step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16909step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16909step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16909step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16909step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16909 raw16909Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw16909 raw16909Labels = mixedMoment B raw16909step0 raw16909step0Labels := by
      have hz : ∀ j, raw16909 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16909step0 = (fun i j => raw16909 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16909step0 raw16909; decide +kernel
      have hl : raw16909step0Labels = raw16909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16909 raw16909Labels permutation346 hz
    mixedMoment B raw16909step0 raw16909step0Labels = mixedMoment B raw16909step1 raw16909step1Labels := by
      have ha : raw16909step1 = (fun i j => raw16909step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16909step1 raw16909step0; decide +kernel
      have hl : raw16909step1Labels = raw16909step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16909step0 raw16909step0Labels permutation151 permutation7
    mixedMoment B raw16909step1 raw16909step1Labels = mixedMoment B raw16909step2 raw16909step2Labels := by
      have ha : raw16909step2 = -raw16909step1 := by apply Matrix.ext; change ∀ i j, raw16909step2 i j = -(raw16909step1 i j); unfold raw16909step2 raw16909step1; decide +kernel
      have hl : raw16909step2Labels = raw16909step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16909step2 raw16909step2Labels = mixedMoment B raw16909step3 raw16909step3Labels := by
      have ha : raw16909step3 = raw16909step2 := by apply Matrix.ext; unfold raw16909step3 raw16909step2; decide +kernel
      have hl : raw16909step2Labels = labelEmbedding1 ∘ raw16909step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16909step2 raw16909step2Labels raw16909step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw16910 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16910Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16910step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16910step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16910step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16910step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16910step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16910 raw16910Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw16910 raw16910Labels = mixedMoment B raw16910step0 raw16910step0Labels := by
      have hz : ∀ j, raw16910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16910step0 = (fun i j => raw16910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16910step0 raw16910; decide +kernel
      have hl : raw16910step0Labels = raw16910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16910 raw16910Labels permutation434 hz
    mixedMoment B raw16910step0 raw16910step0Labels = mixedMoment B raw16910step1 raw16910step1Labels := by
      have ha : raw16910step1 = (fun i j => raw16910step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16910step1 raw16910step0; decide +kernel
      have hl : raw16910step1Labels = raw16910step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16910step0 raw16910step0Labels permutation151 permutation7
    mixedMoment B raw16910step1 raw16910step1Labels = mixedMoment B raw16910step2 raw16910step2Labels := by
      have ha : raw16910step2 = -raw16910step1 := by apply Matrix.ext; change ∀ i j, raw16910step2 i j = -(raw16910step1 i j); unfold raw16910step2 raw16910step1; decide +kernel
      have hl : raw16910step2Labels = raw16910step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16910step2 raw16910step2Labels = mixedMoment B raw16910step3 raw16910step3Labels := by
      have ha : raw16910step3 = raw16910step2 := by apply Matrix.ext; unfold raw16910step3 raw16910step2; decide +kernel
      have hl : raw16910step2Labels = labelEmbedding1 ∘ raw16910step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16910step2 raw16910step2Labels raw16910step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw16911 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16911Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16911step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16911step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16911step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16911 raw16911Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw16911 raw16911Labels = mixedMoment B raw16911step0 raw16911step0Labels := by
      have ha : raw16911step0 = (fun i j => raw16911 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16911step0 raw16911; decide +kernel
      have hl : raw16911step0Labels = raw16911Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16911 raw16911Labels permutation682 permutation7
    mixedMoment B raw16911step0 raw16911step0Labels = mixedMoment B raw16911step1 raw16911step1Labels := by
      have ha : raw16911step1 = -raw16911step0 := by apply Matrix.ext; change ∀ i j, raw16911step1 i j = -(raw16911step0 i j); unfold raw16911step1 raw16911step0; decide +kernel
      have hl : raw16911step1Labels = raw16911step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16911step1 raw16911step1Labels = mixedMoment B raw16911step2 raw16911step2Labels := by
      have ha : raw16911step2 = raw16911step1 := by apply Matrix.ext; unfold raw16911step2 raw16911step1; decide +kernel
      have hl : raw16911step1Labels = labelEmbedding1 ∘ raw16911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16911step1 raw16911step1Labels raw16911step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw16912 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16912Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16912step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16912step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16912step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16912 raw16912Labels = mixedMoment B node3937 node3937Labels := by
  calc
    mixedMoment B raw16912 raw16912Labels = mixedMoment B raw16912step0 raw16912step0Labels := by
      have ha : raw16912step0 = (fun i j => raw16912 (permutation277 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16912step0 raw16912; decide +kernel
      have hl : raw16912step0Labels = raw16912Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16912 raw16912Labels permutation277 permutation5
    mixedMoment B raw16912step0 raw16912step0Labels = mixedMoment B raw16912step1 raw16912step1Labels := by
      have ha : raw16912step1 = -raw16912step0 := by apply Matrix.ext; change ∀ i j, raw16912step1 i j = -(raw16912step0 i j); unfold raw16912step1 raw16912step0; decide +kernel
      have hl : raw16912step1Labels = raw16912step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16912step1 raw16912step1Labels = mixedMoment B raw16912step2 raw16912step2Labels := by
      have ha : raw16912step2 = raw16912step1 := by apply Matrix.ext; unfold raw16912step2 raw16912step1; decide +kernel
      have hl : raw16912step1Labels = labelEmbedding1 ∘ raw16912step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16912step1 raw16912step1Labels raw16912step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3937 node3937Labels := by rfl

def raw16913 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16913Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16913step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16913step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16913step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16913 raw16913Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw16913 raw16913Labels = mixedMoment B raw16913step0 raw16913step0Labels := by
      have ha : raw16913step0 = (fun i j => raw16913 (permutation277 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16913step0 raw16913; decide +kernel
      have hl : raw16913step0Labels = raw16913Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16913 raw16913Labels permutation277 permutation5
    mixedMoment B raw16913step0 raw16913step0Labels = mixedMoment B raw16913step1 raw16913step1Labels := by
      have ha : raw16913step1 = -raw16913step0 := by apply Matrix.ext; change ∀ i j, raw16913step1 i j = -(raw16913step0 i j); unfold raw16913step1 raw16913step0; decide +kernel
      have hl : raw16913step1Labels = raw16913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16913step1 raw16913step1Labels = mixedMoment B raw16913step2 raw16913step2Labels := by
      have ha : raw16913step2 = raw16913step1 := by apply Matrix.ext; unfold raw16913step2 raw16913step1; decide +kernel
      have hl : raw16913step1Labels = labelEmbedding1 ∘ raw16913step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16913step1 raw16913step1Labels raw16913step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2617 node2617Labels := by rfl

def raw16914 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16914Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16914step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16914step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16914step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16914step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16914 raw16914Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw16914 raw16914Labels = mixedMoment B raw16914step0 raw16914step0Labels := by
      have hz : ∀ j, raw16914 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16914step0 = (fun i j => raw16914 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16914step0 raw16914; decide +kernel
      have hl : raw16914step0Labels = raw16914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16914 raw16914Labels permutation346 hz
    mixedMoment B raw16914step0 raw16914step0Labels = mixedMoment B raw16914step1 raw16914step1Labels := by
      have ha : raw16914step1 = (fun i j => raw16914step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16914step1 raw16914step0; decide +kernel
      have hl : raw16914step1Labels = raw16914step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16914step0 raw16914step0Labels permutation58 permutation5
    mixedMoment B raw16914step1 raw16914step1Labels = mixedMoment B raw16914step2 raw16914step2Labels := by
      have ha : raw16914step2 = -raw16914step1 := by apply Matrix.ext; change ∀ i j, raw16914step2 i j = -(raw16914step1 i j); unfold raw16914step2 raw16914step1; decide +kernel
      have hl : raw16914step2Labels = raw16914step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16914step2 raw16914step2Labels = mixedMoment B raw16914step3 raw16914step3Labels := by
      have ha : raw16914step3 = raw16914step2 := by apply Matrix.ext; unfold raw16914step3 raw16914step2; decide +kernel
      have hl : raw16914step2Labels = labelEmbedding1 ∘ raw16914step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16914step2 raw16914step2Labels raw16914step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw16915 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16915Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16915step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16915step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16915step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16915step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16915step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16915 raw16915Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw16915 raw16915Labels = mixedMoment B raw16915step0 raw16915step0Labels := by
      have hz : ∀ j, raw16915 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16915step0 = (fun i j => raw16915 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16915step0 raw16915; decide +kernel
      have hl : raw16915step0Labels = raw16915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16915 raw16915Labels permutation434 hz
    mixedMoment B raw16915step0 raw16915step0Labels = mixedMoment B raw16915step1 raw16915step1Labels := by
      have ha : raw16915step1 = (fun i j => raw16915step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16915step1 raw16915step0; decide +kernel
      have hl : raw16915step1Labels = raw16915step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16915step0 raw16915step0Labels permutation58 permutation5
    mixedMoment B raw16915step1 raw16915step1Labels = mixedMoment B raw16915step2 raw16915step2Labels := by
      have ha : raw16915step2 = -raw16915step1 := by apply Matrix.ext; change ∀ i j, raw16915step2 i j = -(raw16915step1 i j); unfold raw16915step2 raw16915step1; decide +kernel
      have hl : raw16915step2Labels = raw16915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16915step2 raw16915step2Labels = mixedMoment B raw16915step3 raw16915step3Labels := by
      have ha : raw16915step3 = raw16915step2 := by apply Matrix.ext; unfold raw16915step3 raw16915step2; decide +kernel
      have hl : raw16915step2Labels = labelEmbedding1 ∘ raw16915step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16915step2 raw16915step2Labels raw16915step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw16916 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16916Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16916step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16916step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16916step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16916 raw16916Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw16916 raw16916Labels = mixedMoment B raw16916step0 raw16916step0Labels := by
      have ha : raw16916step0 = (fun i j => raw16916 (permutation322 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16916step0 raw16916; decide +kernel
      have hl : raw16916step0Labels = raw16916Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16916 raw16916Labels permutation322 permutation5
    mixedMoment B raw16916step0 raw16916step0Labels = mixedMoment B raw16916step1 raw16916step1Labels := by
      have ha : raw16916step1 = -raw16916step0 := by apply Matrix.ext; change ∀ i j, raw16916step1 i j = -(raw16916step0 i j); unfold raw16916step1 raw16916step0; decide +kernel
      have hl : raw16916step1Labels = raw16916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16916step1 raw16916step1Labels = mixedMoment B raw16916step2 raw16916step2Labels := by
      have ha : raw16916step2 = raw16916step1 := by apply Matrix.ext; unfold raw16916step2 raw16916step1; decide +kernel
      have hl : raw16916step1Labels = labelEmbedding1 ∘ raw16916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16916step1 raw16916step1Labels raw16916step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3949 node3949Labels := by rfl

def raw16917 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16917 raw16917Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw16917 raw16917Labels = mixedMoment B raw16917step0 raw16917step0Labels := by
      have ha : raw16917step0 = (fun i j => raw16917 (permutation277 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16917step0 raw16917; decide +kernel
      have hl : raw16917step0Labels = raw16917Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16917 raw16917Labels permutation277 permutation4
    mixedMoment B raw16917step0 raw16917step0Labels = mixedMoment B raw16917step1 raw16917step1Labels := by
      have ha : raw16917step1 = -raw16917step0 := by apply Matrix.ext; change ∀ i j, raw16917step1 i j = -(raw16917step0 i j); unfold raw16917step1 raw16917step0; decide +kernel
      have hl : raw16917step1Labels = raw16917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw16918 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16918 raw16918Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw16918 raw16918Labels = mixedMoment B raw16918step0 raw16918step0Labels := by
      have ha : raw16918step0 = (fun i j => raw16918 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16918step0 raw16918; decide +kernel
      have hl : raw16918step0Labels = raw16918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16918 raw16918Labels permutation167 permutation4
    mixedMoment B raw16918step0 raw16918step0Labels = mixedMoment B raw16918step1 raw16918step1Labels := by
      have ha : raw16918step1 = -raw16918step0 := by apply Matrix.ext; change ∀ i j, raw16918step1 i j = -(raw16918step0 i j); unfold raw16918step1 raw16918step0; decide +kernel
      have hl : raw16918step1Labels = raw16918step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3691 node3691Labels := by rfl

def raw16919 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16919step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16919 raw16919Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw16919 raw16919Labels = mixedMoment B raw16919step0 raw16919step0Labels := by
      have ha : raw16919step0 = (fun i j => raw16919 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16919step0 raw16919; decide +kernel
      have hl : raw16919step0Labels = raw16919Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16919 raw16919Labels permutation165 permutation4
    mixedMoment B raw16919step0 raw16919step0Labels = mixedMoment B raw16919step1 raw16919step1Labels := by
      have ha : raw16919step1 = -raw16919step0 := by apply Matrix.ext; change ∀ i j, raw16919step1 i j = -(raw16919step0 i j); unfold raw16919step1 raw16919step0; decide +kernel
      have hl : raw16919step1Labels = raw16919step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3691 node3691Labels := by rfl

def raw16920 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16920 raw16920Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw16920 raw16920Labels = mixedMoment B raw16920step0 raw16920step0Labels := by
      have ha : raw16920step0 = (fun i j => raw16920 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16920step0 raw16920; decide +kernel
      have hl : raw16920step0Labels = raw16920Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16920 raw16920Labels permutation152 permutation4
    mixedMoment B raw16920step0 raw16920step0Labels = mixedMoment B raw16920step1 raw16920step1Labels := by
      have ha : raw16920step1 = -raw16920step0 := by apply Matrix.ext; change ∀ i j, raw16920step1 i j = -(raw16920step0 i j); unfold raw16920step1 raw16920step0; decide +kernel
      have hl : raw16920step1Labels = raw16920step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3703 node3703Labels := by rfl

def raw16921 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw16921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16921step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16921 raw16921Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw16921 raw16921Labels = mixedMoment B raw16921step0 raw16921step0Labels := by
      have ha : raw16921step0 = (fun i j => raw16921 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16921step0 raw16921; decide +kernel
      have hl : raw16921step0Labels = raw16921Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16921 raw16921Labels permutation164 permutation4
    mixedMoment B raw16921step0 raw16921step0Labels = mixedMoment B raw16921step1 raw16921step1Labels := by
      have ha : raw16921step1 = -raw16921step0 := by apply Matrix.ext; change ∀ i j, raw16921step1 i j = -(raw16921step0 i j); unfold raw16921step1 raw16921step0; decide +kernel
      have hl : raw16921step1Labels = raw16921step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3689 node3689Labels := by rfl

def raw16922 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16922 raw16922Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw16922 raw16922Labels = mixedMoment B raw16922step0 raw16922step0Labels := by
      have ha : raw16922step0 = (fun i j => raw16922 (permutation277 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16922step0 raw16922; decide +kernel
      have hl : raw16922step0Labels = raw16922Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16922 raw16922Labels permutation277 permutation4
    mixedMoment B raw16922step0 raw16922step0Labels = mixedMoment B raw16922step1 raw16922step1Labels := by
      have ha : raw16922step1 = -raw16922step0 := by apply Matrix.ext; change ∀ i j, raw16922step1 i j = -(raw16922step0 i j); unfold raw16922step1 raw16922step0; decide +kernel
      have hl : raw16922step1Labels = raw16922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3036 node3036Labels := by rfl

def raw16923 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16923step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16923 raw16923Labels = mixedMoment B node2863 node2863Labels := by
  calc
    mixedMoment B raw16923 raw16923Labels = mixedMoment B raw16923step0 raw16923step0Labels := by
      have ha : raw16923step0 = (fun i j => raw16923 (permutation280 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16923step0 raw16923; decide +kernel
      have hl : raw16923step0Labels = raw16923Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16923 raw16923Labels permutation280 permutation4
    mixedMoment B raw16923step0 raw16923step0Labels = mixedMoment B raw16923step1 raw16923step1Labels := by
      have ha : raw16923step1 = -raw16923step0 := by apply Matrix.ext; change ∀ i j, raw16923step1 i j = -(raw16923step0 i j); unfold raw16923step1 raw16923step0; decide +kernel
      have hl : raw16923step1Labels = raw16923step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2863 node2863Labels := by rfl

def raw16924 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16924 raw16924Labels = mixedMoment B node2863 node2863Labels := by
  calc
    mixedMoment B raw16924 raw16924Labels = mixedMoment B raw16924step0 raw16924step0Labels := by
      have ha : raw16924step0 = (fun i j => raw16924 (permutation278 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16924step0 raw16924; decide +kernel
      have hl : raw16924step0Labels = raw16924Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16924 raw16924Labels permutation278 permutation4
    mixedMoment B raw16924step0 raw16924step0Labels = mixedMoment B raw16924step1 raw16924step1Labels := by
      have ha : raw16924step1 = -raw16924step0 := by apply Matrix.ext; change ∀ i j, raw16924step1 i j = -(raw16924step0 i j); unfold raw16924step1 raw16924step0; decide +kernel
      have hl : raw16924step1Labels = raw16924step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2863 node2863Labels := by rfl

def raw16925 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16925 raw16925Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw16925 raw16925Labels = mixedMoment B raw16925step0 raw16925step0Labels := by
      have ha : raw16925step0 = (fun i j => raw16925 (permutation265 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16925step0 raw16925; decide +kernel
      have hl : raw16925step0Labels = raw16925Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16925 raw16925Labels permutation265 permutation4
    mixedMoment B raw16925step0 raw16925step0Labels = mixedMoment B raw16925step1 raw16925step1Labels := by
      have ha : raw16925step1 = -raw16925step0 := by apply Matrix.ext; change ∀ i j, raw16925step1 i j = -(raw16925step0 i j); unfold raw16925step1 raw16925step0; decide +kernel
      have hl : raw16925step1Labels = raw16925step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2878 node2878Labels := by rfl

def raw16926 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw16926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16926 raw16926Labels = mixedMoment B node2861 node2861Labels := by
  calc
    mixedMoment B raw16926 raw16926Labels = mixedMoment B raw16926step0 raw16926step0Labels := by
      have ha : raw16926step0 = (fun i j => raw16926 (permutation277 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16926step0 raw16926; decide +kernel
      have hl : raw16926step0Labels = raw16926Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16926 raw16926Labels permutation277 permutation4
    mixedMoment B raw16926step0 raw16926step0Labels = mixedMoment B raw16926step1 raw16926step1Labels := by
      have ha : raw16926step1 = -raw16926step0 := by apply Matrix.ext; change ∀ i j, raw16926step1 i j = -(raw16926step0 i j); unfold raw16926step1 raw16926step0; decide +kernel
      have hl : raw16926step1Labels = raw16926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2861 node2861Labels := by rfl

def raw16927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16927step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16927step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16927step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16927step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16927 raw16927Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw16927 raw16927Labels = mixedMoment B raw16927step0 raw16927step0Labels := by
      have ha : raw16927step0 = (fun i j => raw16927 (permutation456 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16927step0 raw16927; decide +kernel
      have hl : raw16927step0Labels = raw16927Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16927 raw16927Labels permutation456 permutation4
    mixedMoment B raw16927step0 raw16927step0Labels = mixedMoment B raw16927step1 raw16927step1Labels := by
      have ha : raw16927step1 = -raw16927step0 := by apply Matrix.ext; change ∀ i j, raw16927step1 i j = -(raw16927step0 i j); unfold raw16927step1 raw16927step0; decide +kernel
      have hl : raw16927step1Labels = raw16927step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16927step1 raw16927step1Labels = mixedMoment B raw16927step2 raw16927step2Labels := by
      have ha : raw16927step2 = raw16927step1 := by apply Matrix.ext; unfold raw16927step2 raw16927step1; decide +kernel
      have hl : raw16927step1Labels = labelEmbedding7 ∘ raw16927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16927step1 raw16927step1Labels raw16927step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw16928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw16928step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16928step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw16928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16928 raw16928Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw16928 raw16928Labels = mixedMoment B raw16928step0 raw16928step0Labels := by
      have ha : raw16928step0 = (fun i j => raw16928 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16928step0 raw16928; decide +kernel
      have hl : raw16928step0Labels = raw16928Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16928 raw16928Labels permutation514 permutation6
    mixedMoment B raw16928step0 raw16928step0Labels = mixedMoment B raw16928step1 raw16928step1Labels := by
      have ha : raw16928step1 = raw16928step0 := by apply Matrix.ext; unfold raw16928step1 raw16928step0; decide +kernel
      have hl : raw16928step0Labels = labelEmbedding9 ∘ raw16928step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16928step0 raw16928step0Labels raw16928step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw16929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16929step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16929step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16929step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16929step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16929 raw16929Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw16929 raw16929Labels = mixedMoment B raw16929step0 raw16929step0Labels := by
      have ha : raw16929step0 = (fun i j => raw16929 (permutation439 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16929step0 raw16929; decide +kernel
      have hl : raw16929step0Labels = raw16929Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16929 raw16929Labels permutation439 permutation4
    mixedMoment B raw16929step0 raw16929step0Labels = mixedMoment B raw16929step1 raw16929step1Labels := by
      have ha : raw16929step1 = -raw16929step0 := by apply Matrix.ext; change ∀ i j, raw16929step1 i j = -(raw16929step0 i j); unfold raw16929step1 raw16929step0; decide +kernel
      have hl : raw16929step1Labels = raw16929step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16929step1 raw16929step1Labels = mixedMoment B raw16929step2 raw16929step2Labels := by
      have ha : raw16929step2 = raw16929step1 := by apply Matrix.ext; unfold raw16929step2 raw16929step1; decide +kernel
      have hl : raw16929step1Labels = labelEmbedding7 ∘ raw16929step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16929step1 raw16929step1Labels raw16929step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw16930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16930step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16930step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16930 raw16930Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw16930 raw16930Labels = mixedMoment B raw16930step0 raw16930step0Labels := by
      have hz : ∀ j, raw16930 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16930step0 = (fun i j => raw16930 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16930step0 raw16930; decide +kernel
      have hl : raw16930step0Labels = raw16930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16930 raw16930Labels permutation520 hz
    mixedMoment B raw16930step0 raw16930step0Labels = mixedMoment B raw16930step1 raw16930step1Labels := by
      have ha : raw16930step1 = (fun i j => raw16930step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16930step1 raw16930step0; decide +kernel
      have hl : raw16930step1Labels = raw16930step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16930step0 raw16930step0Labels permutation122 permutation6
    mixedMoment B raw16930step1 raw16930step1Labels = mixedMoment B raw16930step2 raw16930step2Labels := by
      have ha : raw16930step2 = raw16930step1 := by apply Matrix.ext; unfold raw16930step2 raw16930step1; decide +kernel
      have hl : raw16930step1Labels = labelEmbedding9 ∘ raw16930step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16930step1 raw16930step1Labels raw16930step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw16931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16931step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16931step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16931 raw16931Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw16931 raw16931Labels = mixedMoment B raw16931step0 raw16931step0Labels := by
      have ha : raw16931step0 = (fun i j => raw16931 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16931step0 raw16931; decide +kernel
      have hl : raw16931step0Labels = raw16931Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16931 raw16931Labels permutation514 permutation6
    mixedMoment B raw16931step0 raw16931step0Labels = mixedMoment B raw16931step1 raw16931step1Labels := by
      have ha : raw16931step1 = raw16931step0 := by apply Matrix.ext; unfold raw16931step1 raw16931step0; decide +kernel
      have hl : raw16931step0Labels = labelEmbedding9 ∘ raw16931step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16931step0 raw16931step0Labels raw16931step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw16932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16932step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16932 raw16932Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw16932 raw16932Labels = mixedMoment B raw16932step0 raw16932step0Labels := by
      have ha : raw16932step0 = (fun i j => raw16932 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16932step0 raw16932; decide +kernel
      have hl : raw16932step0Labels = raw16932Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16932 raw16932Labels permutation200 permutation3
    mixedMoment B raw16932step0 raw16932step0Labels = mixedMoment B raw16932step1 raw16932step1Labels := by
      have ha : raw16932step1 = raw16932step0 := by apply Matrix.ext; unfold raw16932step1 raw16932step0; decide +kernel
      have hl : raw16932step0Labels = labelEmbedding6 ∘ raw16932step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16932step0 raw16932step0Labels raw16932step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

def raw16933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16933step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16933step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16933step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16933step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16933 raw16933Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw16933 raw16933Labels = mixedMoment B raw16933step0 raw16933step0Labels := by
      have ha : raw16933step0 = (fun i j => raw16933 (permutation442 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16933step0 raw16933; decide +kernel
      have hl : raw16933step0Labels = raw16933Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16933 raw16933Labels permutation442 permutation4
    mixedMoment B raw16933step0 raw16933step0Labels = mixedMoment B raw16933step1 raw16933step1Labels := by
      have ha : raw16933step1 = -raw16933step0 := by apply Matrix.ext; change ∀ i j, raw16933step1 i j = -(raw16933step0 i j); unfold raw16933step1 raw16933step0; decide +kernel
      have hl : raw16933step1Labels = raw16933step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16933step1 raw16933step1Labels = mixedMoment B raw16933step2 raw16933step2Labels := by
      have ha : raw16933step2 = raw16933step1 := by apply Matrix.ext; unfold raw16933step2 raw16933step1; decide +kernel
      have hl : raw16933step1Labels = labelEmbedding7 ∘ raw16933step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16933step1 raw16933step1Labels raw16933step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw16934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16934step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16934step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16934step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16934step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16934 raw16934Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw16934 raw16934Labels = mixedMoment B raw16934step0 raw16934step0Labels := by
      have ha : raw16934step0 = (fun i j => raw16934 (permutation449 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16934step0 raw16934; decide +kernel
      have hl : raw16934step0Labels = raw16934Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16934 raw16934Labels permutation449 permutation4
    mixedMoment B raw16934step0 raw16934step0Labels = mixedMoment B raw16934step1 raw16934step1Labels := by
      have ha : raw16934step1 = -raw16934step0 := by apply Matrix.ext; change ∀ i j, raw16934step1 i j = -(raw16934step0 i j); unfold raw16934step1 raw16934step0; decide +kernel
      have hl : raw16934step1Labels = raw16934step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16934step1 raw16934step1Labels = mixedMoment B raw16934step2 raw16934step2Labels := by
      have ha : raw16934step2 = raw16934step1 := by apply Matrix.ext; unfold raw16934step2 raw16934step1; decide +kernel
      have hl : raw16934step1Labels = labelEmbedding7 ∘ raw16934step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16934step1 raw16934step1Labels raw16934step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw16935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16935step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16935step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16935step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16935step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16935 raw16935Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw16935 raw16935Labels = mixedMoment B raw16935step0 raw16935step0Labels := by
      have hz : ∀ j, raw16935 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16935step0 = (fun i j => raw16935 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16935step0 raw16935; decide +kernel
      have hl : raw16935step0Labels = raw16935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16935 raw16935Labels permutation520 hz
    mixedMoment B raw16935step0 raw16935step0Labels = mixedMoment B raw16935step1 raw16935step1Labels := by
      have ha : raw16935step1 = (fun i j => raw16935step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16935step1 raw16935step0; decide +kernel
      have hl : raw16935step1Labels = raw16935step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16935step0 raw16935step0Labels permutation108 permutation4
    mixedMoment B raw16935step1 raw16935step1Labels = mixedMoment B raw16935step2 raw16935step2Labels := by
      have ha : raw16935step2 = -raw16935step1 := by apply Matrix.ext; change ∀ i j, raw16935step2 i j = -(raw16935step1 i j); unfold raw16935step2 raw16935step1; decide +kernel
      have hl : raw16935step2Labels = raw16935step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16935step2 raw16935step2Labels = mixedMoment B raw16935step3 raw16935step3Labels := by
      have ha : raw16935step3 = raw16935step2 := by apply Matrix.ext; unfold raw16935step3 raw16935step2; decide +kernel
      have hl : raw16935step2Labels = labelEmbedding7 ∘ raw16935step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16935step2 raw16935step2Labels raw16935step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw16936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16936step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16936step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16936 raw16936Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw16936 raw16936Labels = mixedMoment B raw16936step0 raw16936step0Labels := by
      have ha : raw16936step0 = (fun i j => raw16936 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16936step0 raw16936; decide +kernel
      have hl : raw16936step0Labels = raw16936Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16936 raw16936Labels permutation514 permutation6
    mixedMoment B raw16936step0 raw16936step0Labels = mixedMoment B raw16936step1 raw16936step1Labels := by
      have ha : raw16936step1 = raw16936step0 := by apply Matrix.ext; unfold raw16936step1 raw16936step0; decide +kernel
      have hl : raw16936step0Labels = labelEmbedding9 ∘ raw16936step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16936step0 raw16936step0Labels raw16936step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw16937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16937step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16937step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16937 raw16937Labels = mixedMoment B node5124 node5124Labels := by
  calc
    mixedMoment B raw16937 raw16937Labels = mixedMoment B raw16937step0 raw16937step0Labels := by
      have ha : raw16937step0 = (fun i j => raw16937 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16937step0 raw16937; decide +kernel
      have hl : raw16937step0Labels = raw16937Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16937 raw16937Labels permutation160 permutation3
    mixedMoment B raw16937step0 raw16937step0Labels = mixedMoment B raw16937step1 raw16937step1Labels := by
      have ha : raw16937step1 = raw16937step0 := by apply Matrix.ext; unfold raw16937step1 raw16937step0; decide +kernel
      have hl : raw16937step0Labels = labelEmbedding6 ∘ raw16937step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16937step0 raw16937step0Labels raw16937step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5124 node5124Labels := by rfl

def raw16938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16938step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw16938step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16938step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw16938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16938 raw16938Labels = mixedMoment B node5444 node5444Labels := by
  calc
    mixedMoment B raw16938 raw16938Labels = mixedMoment B raw16938step0 raw16938step0Labels := by
      have ha : raw16938step0 = (fun i j => raw16938 (permutation439 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16938step0 raw16938; decide +kernel
      have hl : raw16938step0Labels = raw16938Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16938 raw16938Labels permutation439 permutation4
    mixedMoment B raw16938step0 raw16938step0Labels = mixedMoment B raw16938step1 raw16938step1Labels := by
      have ha : raw16938step1 = -raw16938step0 := by apply Matrix.ext; change ∀ i j, raw16938step1 i j = -(raw16938step0 i j); unfold raw16938step1 raw16938step0; decide +kernel
      have hl : raw16938step1Labels = raw16938step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16938step1 raw16938step1Labels = mixedMoment B raw16938step2 raw16938step2Labels := by
      have ha : raw16938step2 = raw16938step1 := by apply Matrix.ext; unfold raw16938step2 raw16938step1; decide +kernel
      have hl : raw16938step1Labels = labelEmbedding7 ∘ raw16938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16938step1 raw16938step1Labels raw16938step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5444 node5444Labels := by rfl

def raw16939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16939step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw16939step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16939step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw16939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16939 raw16939Labels = mixedMoment B node5190 node5190Labels := by
  calc
    mixedMoment B raw16939 raw16939Labels = mixedMoment B raw16939step0 raw16939step0Labels := by
      have ha : raw16939step0 = (fun i j => raw16939 (permutation439 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16939step0 raw16939; decide +kernel
      have hl : raw16939step0Labels = raw16939Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16939 raw16939Labels permutation439 permutation4
    mixedMoment B raw16939step0 raw16939step0Labels = mixedMoment B raw16939step1 raw16939step1Labels := by
      have ha : raw16939step1 = -raw16939step0 := by apply Matrix.ext; change ∀ i j, raw16939step1 i j = -(raw16939step0 i j); unfold raw16939step1 raw16939step0; decide +kernel
      have hl : raw16939step1Labels = raw16939step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16939step1 raw16939step1Labels = mixedMoment B raw16939step2 raw16939step2Labels := by
      have ha : raw16939step2 = raw16939step1 := by apply Matrix.ext; unfold raw16939step2 raw16939step1; decide +kernel
      have hl : raw16939step1Labels = labelEmbedding7 ∘ raw16939step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16939step1 raw16939step1Labels raw16939step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5190 node5190Labels := by rfl

def raw16940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16940step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16940step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16940step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16940step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16940 raw16940Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw16940 raw16940Labels = mixedMoment B raw16940step0 raw16940step0Labels := by
      have hz : ∀ j, raw16940 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16940step0 = (fun i j => raw16940 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16940step0 raw16940; decide +kernel
      have hl : raw16940step0Labels = raw16940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16940 raw16940Labels permutation520 hz
    mixedMoment B raw16940step0 raw16940step0Labels = mixedMoment B raw16940step1 raw16940step1Labels := by
      have ha : raw16940step1 = (fun i j => raw16940step0 (permutation105 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16940step1 raw16940step0; decide +kernel
      have hl : raw16940step1Labels = raw16940step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16940step0 raw16940step0Labels permutation105 permutation4
    mixedMoment B raw16940step1 raw16940step1Labels = mixedMoment B raw16940step2 raw16940step2Labels := by
      have ha : raw16940step2 = -raw16940step1 := by apply Matrix.ext; change ∀ i j, raw16940step2 i j = -(raw16940step1 i j); unfold raw16940step2 raw16940step1; decide +kernel
      have hl : raw16940step2Labels = raw16940step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16940step2 raw16940step2Labels = mixedMoment B raw16940step3 raw16940step3Labels := by
      have ha : raw16940step3 = raw16940step2 := by apply Matrix.ext; unfold raw16940step3 raw16940step2; decide +kernel
      have hl : raw16940step2Labels = labelEmbedding7 ∘ raw16940step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16940step2 raw16940step2Labels raw16940step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw16941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16941step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16941 raw16941Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw16941 raw16941Labels = mixedMoment B raw16941step0 raw16941step0Labels := by
      have ha : raw16941step0 = (fun i j => raw16941 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16941step0 raw16941; decide +kernel
      have hl : raw16941step0Labels = raw16941Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16941 raw16941Labels permutation514 permutation6
    mixedMoment B raw16941step0 raw16941step0Labels = mixedMoment B raw16941step1 raw16941step1Labels := by
      have ha : raw16941step1 = raw16941step0 := by apply Matrix.ext; unfold raw16941step1 raw16941step0; decide +kernel
      have hl : raw16941step0Labels = labelEmbedding9 ∘ raw16941step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16941step0 raw16941step0Labels raw16941step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw16942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16942step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16942 raw16942Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw16942 raw16942Labels = mixedMoment B raw16942step0 raw16942step0Labels := by
      have ha : raw16942step0 = (fun i j => raw16942 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16942step0 raw16942; decide +kernel
      have hl : raw16942step0Labels = raw16942Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16942 raw16942Labels permutation152 permutation3
    mixedMoment B raw16942step0 raw16942step0Labels = mixedMoment B raw16942step1 raw16942step1Labels := by
      have ha : raw16942step1 = raw16942step0 := by apply Matrix.ext; unfold raw16942step1 raw16942step0; decide +kernel
      have hl : raw16942step0Labels = labelEmbedding6 ∘ raw16942step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16942step0 raw16942step0Labels raw16942step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw16943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16943 raw16943Labels = mixedMoment B node5459 node5459Labels := by
  calc
    mixedMoment B raw16943 raw16943Labels = mixedMoment B raw16943step0 raw16943step0Labels := by
      have ha : raw16943step0 = (fun i j => raw16943 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16943step0 raw16943; decide +kernel
      have hl : raw16943step0Labels = raw16943Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16943 raw16943Labels permutation154 permutation2
    _ = mixedMoment B node5459 node5459Labels := by rfl

def raw16944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw16944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16944step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16944 raw16944Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw16944 raw16944Labels = mixedMoment B raw16944step0 raw16944step0Labels := by
      have ha : raw16944step0 = (fun i j => raw16944 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16944step0 raw16944; decide +kernel
      have hl : raw16944step0Labels = raw16944Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16944 raw16944Labels permutation662 permutation2
    mixedMoment B raw16944step0 raw16944step0Labels = mixedMoment B raw16944step1 raw16944step1Labels := by
      have ha : raw16944step1 = -raw16944step0 := by apply Matrix.ext; change ∀ i j, raw16944step1 i j = -(raw16944step0 i j); unfold raw16944step1 raw16944step0; decide +kernel
      have hl : raw16944step1Labels = raw16944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw16945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw16945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16945step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16945 raw16945Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16945 raw16945Labels = mixedMoment B raw16945step0 raw16945step0Labels := by
      have hz : ∀ j, raw16945 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16945step0 = (fun i j => raw16945 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16945step0 raw16945; decide +kernel
      have hl : raw16945step0Labels = raw16945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16945 raw16945Labels permutation520 hz
    mixedMoment B raw16945step0 raw16945step0Labels = mixedMoment B raw16945step1 raw16945step1Labels := by
      have ha : raw16945step1 = (fun i j => raw16945step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16945step1 raw16945step0; decide +kernel
      have hl : raw16945step1Labels = raw16945step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16945step0 raw16945step0Labels permutation151 permutation2
    mixedMoment B raw16945step1 raw16945step1Labels = mixedMoment B raw16945step2 raw16945step2Labels := by
      have ha : raw16945step2 = -raw16945step1 := by apply Matrix.ext; change ∀ i j, raw16945step2 i j = -(raw16945step1 i j); unfold raw16945step2 raw16945step1; decide +kernel
      have hl : raw16945step2Labels = raw16945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw16946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16946 raw16946Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw16946 raw16946Labels = mixedMoment B raw16946step0 raw16946step0Labels := by
      have ha : raw16946step0 = (fun i j => raw16946 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16946step0 raw16946; decide +kernel
      have hl : raw16946step0Labels = raw16946Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16946 raw16946Labels permutation155 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw16947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw16947step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw16947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16947 raw16947Labels = mixedMoment B node5121 node5121Labels := by
  calc
    mixedMoment B raw16947 raw16947Labels = mixedMoment B raw16947step0 raw16947step0Labels := by
      have ha : raw16947step0 = (fun i j => raw16947 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16947step0 raw16947; decide +kernel
      have hl : raw16947step0Labels = raw16947Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16947 raw16947Labels permutation159 permutation3
    mixedMoment B raw16947step0 raw16947step0Labels = mixedMoment B raw16947step1 raw16947step1Labels := by
      have ha : raw16947step1 = raw16947step0 := by apply Matrix.ext; unfold raw16947step1 raw16947step0; decide +kernel
      have hl : raw16947step0Labels = labelEmbedding6 ∘ raw16947step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16947step0 raw16947step0Labels raw16947step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5121 node5121Labels := by rfl

def raw16948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw16948step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16948step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16948step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16948step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16948 raw16948Labels = mixedMoment B node5343 node5343Labels := by
  calc
    mixedMoment B raw16948 raw16948Labels = mixedMoment B raw16948step0 raw16948step0Labels := by
      have ha : raw16948step0 = (fun i j => raw16948 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16948step0 raw16948; decide +kernel
      have hl : raw16948step0Labels = raw16948Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16948 raw16948Labels permutation583 permutation3
    mixedMoment B raw16948step0 raw16948step0Labels = mixedMoment B raw16948step1 raw16948step1Labels := by
      have ha : raw16948step1 = -raw16948step0 := by apply Matrix.ext; change ∀ i j, raw16948step1 i j = -(raw16948step0 i j); unfold raw16948step1 raw16948step0; decide +kernel
      have hl : raw16948step1Labels = raw16948step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16948step1 raw16948step1Labels = mixedMoment B raw16948step2 raw16948step2Labels := by
      have ha : raw16948step2 = raw16948step1 := by apply Matrix.ext; unfold raw16948step2 raw16948step1; decide +kernel
      have hl : raw16948step1Labels = labelEmbedding6 ∘ raw16948step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16948step1 raw16948step1Labels raw16948step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5343 node5343Labels := by rfl

def raw16949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw16949step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16949step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16949step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16949 raw16949Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw16949 raw16949Labels = mixedMoment B raw16949step0 raw16949step0Labels := by
      have ha : raw16949step0 = (fun i j => raw16949 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16949step0 raw16949; decide +kernel
      have hl : raw16949step0Labels = raw16949Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16949 raw16949Labels permutation587 permutation3
    mixedMoment B raw16949step0 raw16949step0Labels = mixedMoment B raw16949step1 raw16949step1Labels := by
      have ha : raw16949step1 = -raw16949step0 := by apply Matrix.ext; change ∀ i j, raw16949step1 i j = -(raw16949step0 i j); unfold raw16949step1 raw16949step0; decide +kernel
      have hl : raw16949step1Labels = raw16949step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16949step1 raw16949step1Labels = mixedMoment B raw16949step2 raw16949step2Labels := by
      have ha : raw16949step2 = raw16949step1 := by apply Matrix.ext; unfold raw16949step2 raw16949step1; decide +kernel
      have hl : raw16949step1Labels = labelEmbedding6 ∘ raw16949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16949step1 raw16949step1Labels raw16949step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw16950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16950step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16950step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16950step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16950 raw16950Labels = mixedMoment B node5191 node5191Labels := by
  calc
    mixedMoment B raw16950 raw16950Labels = mixedMoment B raw16950step0 raw16950step0Labels := by
      have ha : raw16950step0 = (fun i j => raw16950 (permutation438 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16950step0 raw16950; decide +kernel
      have hl : raw16950step0Labels = raw16950Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16950 raw16950Labels permutation438 permutation4
    mixedMoment B raw16950step0 raw16950step0Labels = mixedMoment B raw16950step1 raw16950step1Labels := by
      have ha : raw16950step1 = -raw16950step0 := by apply Matrix.ext; change ∀ i j, raw16950step1 i j = -(raw16950step0 i j); unfold raw16950step1 raw16950step0; decide +kernel
      have hl : raw16950step1Labels = raw16950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16950step1 raw16950step1Labels = mixedMoment B raw16950step2 raw16950step2Labels := by
      have ha : raw16950step2 = raw16950step1 := by apply Matrix.ext; unfold raw16950step2 raw16950step1; decide +kernel
      have hl : raw16950step1Labels = labelEmbedding7 ∘ raw16950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16950step1 raw16950step1Labels raw16950step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5191 node5191Labels := by rfl

def raw16951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw16951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16951step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16951 raw16951Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw16951 raw16951Labels = mixedMoment B raw16951step0 raw16951step0Labels := by
      have ha : raw16951step0 = (fun i j => raw16951 (permutation549 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16951step0 raw16951; decide +kernel
      have hl : raw16951step0Labels = raw16951Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16951 raw16951Labels permutation549 permutation5
    mixedMoment B raw16951step0 raw16951step0Labels = mixedMoment B raw16951step1 raw16951step1Labels := by
      have ha : raw16951step1 = raw16951step0 := by apply Matrix.ext; unfold raw16951step1 raw16951step0; decide +kernel
      have hl : raw16951step0Labels = labelEmbedding8 ∘ raw16951step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16951step0 raw16951step0Labels raw16951step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw16952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw16952step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw16952step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16952step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw16952step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16952 raw16952Labels = mixedMoment B node5051 node5051Labels := by
  calc
    mixedMoment B raw16952 raw16952Labels = mixedMoment B raw16952step0 raw16952step0Labels := by
      have ha : raw16952step0 = (fun i j => raw16952 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16952step0 raw16952; decide +kernel
      have hl : raw16952step0Labels = raw16952Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16952 raw16952Labels permutation682 permutation3
    mixedMoment B raw16952step0 raw16952step0Labels = mixedMoment B raw16952step1 raw16952step1Labels := by
      have ha : raw16952step1 = -raw16952step0 := by apply Matrix.ext; change ∀ i j, raw16952step1 i j = -(raw16952step0 i j); unfold raw16952step1 raw16952step0; decide +kernel
      have hl : raw16952step1Labels = raw16952step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16952step1 raw16952step1Labels = mixedMoment B raw16952step2 raw16952step2Labels := by
      have ha : raw16952step2 = raw16952step1 := by apply Matrix.ext; unfold raw16952step2 raw16952step1; decide +kernel
      have hl : raw16952step1Labels = labelEmbedding6 ∘ raw16952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16952step1 raw16952step1Labels raw16952step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5051 node5051Labels := by rfl

def raw16953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw16953step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16953step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16953step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16953 raw16953Labels = mixedMoment B node5054 node5054Labels := by
  calc
    mixedMoment B raw16953 raw16953Labels = mixedMoment B raw16953step0 raw16953step0Labels := by
      have ha : raw16953step0 = (fun i j => raw16953 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16953step0 raw16953; decide +kernel
      have hl : raw16953step0Labels = raw16953Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16953 raw16953Labels permutation681 permutation3
    mixedMoment B raw16953step0 raw16953step0Labels = mixedMoment B raw16953step1 raw16953step1Labels := by
      have ha : raw16953step1 = -raw16953step0 := by apply Matrix.ext; change ∀ i j, raw16953step1 i j = -(raw16953step0 i j); unfold raw16953step1 raw16953step0; decide +kernel
      have hl : raw16953step1Labels = raw16953step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16953step1 raw16953step1Labels = mixedMoment B raw16953step2 raw16953step2Labels := by
      have ha : raw16953step2 = raw16953step1 := by apply Matrix.ext; unfold raw16953step2 raw16953step1; decide +kernel
      have hl : raw16953step1Labels = labelEmbedding6 ∘ raw16953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16953step1 raw16953step1Labels raw16953step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5054 node5054Labels := by rfl

def raw16954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw16954step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16954step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16954step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16954step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16954 raw16954Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw16954 raw16954Labels = mixedMoment B raw16954step0 raw16954step0Labels := by
      have ha : raw16954step0 = (fun i j => raw16954 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16954step0 raw16954; decide +kernel
      have hl : raw16954step0Labels = raw16954Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16954 raw16954Labels permutation686 permutation3
    mixedMoment B raw16954step0 raw16954step0Labels = mixedMoment B raw16954step1 raw16954step1Labels := by
      have ha : raw16954step1 = -raw16954step0 := by apply Matrix.ext; change ∀ i j, raw16954step1 i j = -(raw16954step0 i j); unfold raw16954step1 raw16954step0; decide +kernel
      have hl : raw16954step1Labels = raw16954step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16954step1 raw16954step1Labels = mixedMoment B raw16954step2 raw16954step2Labels := by
      have ha : raw16954step2 = raw16954step1 := by apply Matrix.ext; unfold raw16954step2 raw16954step1; decide +kernel
      have hl : raw16954step1Labels = labelEmbedding6 ∘ raw16954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16954step1 raw16954step1Labels raw16954step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw16955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw16955step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16955step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16955step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16955 raw16955Labels = mixedMoment B node5057 node5057Labels := by
  calc
    mixedMoment B raw16955 raw16955Labels = mixedMoment B raw16955step0 raw16955step0Labels := by
      have ha : raw16955step0 = (fun i j => raw16955 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16955step0 raw16955; decide +kernel
      have hl : raw16955step0Labels = raw16955Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16955 raw16955Labels permutation680 permutation3
    mixedMoment B raw16955step0 raw16955step0Labels = mixedMoment B raw16955step1 raw16955step1Labels := by
      have ha : raw16955step1 = -raw16955step0 := by apply Matrix.ext; change ∀ i j, raw16955step1 i j = -(raw16955step0 i j); unfold raw16955step1 raw16955step0; decide +kernel
      have hl : raw16955step1Labels = raw16955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16955step1 raw16955step1Labels = mixedMoment B raw16955step2 raw16955step2Labels := by
      have ha : raw16955step2 = raw16955step1 := by apply Matrix.ext; unfold raw16955step2 raw16955step1; decide +kernel
      have hl : raw16955step1Labels = labelEmbedding6 ∘ raw16955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16955step1 raw16955step1Labels raw16955step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5057 node5057Labels := by rfl

def raw16956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw16956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw16956step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16956step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16956step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16956step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16956 raw16956Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw16956 raw16956Labels = mixedMoment B raw16956step0 raw16956step0Labels := by
      have hz : ∀ j, raw16956 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16956step0 = (fun i j => raw16956 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16956step0 raw16956; decide +kernel
      have hl : raw16956step0Labels = raw16956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16956 raw16956Labels permutation520 hz
    mixedMoment B raw16956step0 raw16956step0Labels = mixedMoment B raw16956step1 raw16956step1Labels := by
      have ha : raw16956step1 = (fun i j => raw16956step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16956step1 raw16956step0; decide +kernel
      have hl : raw16956step1Labels = raw16956step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16956step0 raw16956step0Labels permutation145 permutation3
    mixedMoment B raw16956step1 raw16956step1Labels = mixedMoment B raw16956step2 raw16956step2Labels := by
      have ha : raw16956step2 = -raw16956step1 := by apply Matrix.ext; change ∀ i j, raw16956step2 i j = -(raw16956step1 i j); unfold raw16956step2 raw16956step1; decide +kernel
      have hl : raw16956step2Labels = raw16956step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16956step2 raw16956step2Labels = mixedMoment B raw16956step3 raw16956step3Labels := by
      have ha : raw16956step3 = raw16956step2 := by apply Matrix.ext; unfold raw16956step3 raw16956step2; decide +kernel
      have hl : raw16956step2Labels = labelEmbedding6 ∘ raw16956step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16956step2 raw16956step2Labels raw16956step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw16957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16957step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16957 raw16957Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw16957 raw16957Labels = mixedMoment B raw16957step0 raw16957step0Labels := by
      have ha : raw16957step0 = (fun i j => raw16957 (permutation516 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16957step0 raw16957; decide +kernel
      have hl : raw16957step0Labels = raw16957Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16957 raw16957Labels permutation516 permutation6
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw16958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw16958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16958 raw16958Labels = mixedMoment B node3882 node3882Labels := by
  calc
    mixedMoment B raw16958 raw16958Labels = mixedMoment B raw16958step0 raw16958step0Labels := by
      have ha : raw16958step0 = (fun i j => raw16958 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16958step0 raw16958; decide +kernel
      have hl : raw16958step0Labels = raw16958Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16958 raw16958Labels permutation514 permutation6
    _ = mixedMoment B node3882 node3882Labels := by rfl

def raw16959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16959 raw16959Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw16959 raw16959Labels = mixedMoment B raw16959step0 raw16959step0Labels := by
      have ha : raw16959step0 = (fun i j => raw16959 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16959step0 raw16959; decide +kernel
      have hl : raw16959step0Labels = raw16959Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16959 raw16959Labels permutation514 permutation6
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw16960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16960 raw16960Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw16960 raw16960Labels = mixedMoment B raw16960step0 raw16960step0Labels := by
      have hz : ∀ j, raw16960 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16960step0 = (fun i j => raw16960 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16960step0 raw16960; decide +kernel
      have hl : raw16960step0Labels = raw16960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16960 raw16960Labels permutation520 hz
    mixedMoment B raw16960step0 raw16960step0Labels = mixedMoment B raw16960step1 raw16960step1Labels := by
      have ha : raw16960step1 = (fun i j => raw16960step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16960step1 raw16960step0; decide +kernel
      have hl : raw16960step1Labels = raw16960step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16960step0 raw16960step0Labels permutation122 permutation6
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw16961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16961 raw16961Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw16961 raw16961Labels = mixedMoment B raw16961step0 raw16961step0Labels := by
      have ha : raw16961step0 = (fun i j => raw16961 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16961step0 raw16961; decide +kernel
      have hl : raw16961step0Labels = raw16961Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16961 raw16961Labels permutation514 permutation6
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw16962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16962 raw16962Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw16962 raw16962Labels = mixedMoment B raw16962step0 raw16962step0Labels := by
      have ha : raw16962step0 = (fun i j => raw16962 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16962step0 raw16962; decide +kernel
      have hl : raw16962step0Labels = raw16962Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16962 raw16962Labels permutation200 permutation3
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw16963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16963 raw16963Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw16963 raw16963Labels = mixedMoment B raw16963step0 raw16963step0Labels := by
      have ha : raw16963step0 = (fun i j => raw16963 (permutation515 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16963step0 raw16963; decide +kernel
      have hl : raw16963step0Labels = raw16963Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16963 raw16963Labels permutation515 permutation6
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw16964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16964 raw16964Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw16964 raw16964Labels = mixedMoment B raw16964step0 raw16964step0Labels := by
      have ha : raw16964step0 = (fun i j => raw16964 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16964step0 raw16964; decide +kernel
      have hl : raw16964step0Labels = raw16964Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16964 raw16964Labels permutation514 permutation6
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw16965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16965 raw16965Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw16965 raw16965Labels = mixedMoment B raw16965step0 raw16965step0Labels := by
      have hz : ∀ j, raw16965 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16965step0 = (fun i j => raw16965 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16965step0 raw16965; decide +kernel
      have hl : raw16965step0Labels = raw16965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16965 raw16965Labels permutation520 hz
    mixedMoment B raw16965step0 raw16965step0Labels = mixedMoment B raw16965step1 raw16965step1Labels := by
      have ha : raw16965step1 = (fun i j => raw16965step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16965step1 raw16965step0; decide +kernel
      have hl : raw16965step1Labels = raw16965step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16965step0 raw16965step0Labels permutation122 permutation6
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw16966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16966 raw16966Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw16966 raw16966Labels = mixedMoment B raw16966step0 raw16966step0Labels := by
      have ha : raw16966step0 = (fun i j => raw16966 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16966step0 raw16966; decide +kernel
      have hl : raw16966step0Labels = raw16966Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16966 raw16966Labels permutation514 permutation6
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw16967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16967 raw16967Labels = mixedMoment B node2537 node2537Labels := by
  calc
    mixedMoment B raw16967 raw16967Labels = mixedMoment B raw16967step0 raw16967step0Labels := by
      have ha : raw16967step0 = (fun i j => raw16967 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16967step0 raw16967; decide +kernel
      have hl : raw16967step0Labels = raw16967Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16967 raw16967Labels permutation160 permutation3
    _ = mixedMoment B node2537 node2537Labels := by rfl

def raw16968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw16968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16968 raw16968Labels = mixedMoment B node3879 node3879Labels := by
  calc
    mixedMoment B raw16968 raw16968Labels = mixedMoment B raw16968step0 raw16968step0Labels := by
      have ha : raw16968step0 = (fun i j => raw16968 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16968step0 raw16968; decide +kernel
      have hl : raw16968step0Labels = raw16968Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16968 raw16968Labels permutation514 permutation6
    _ = mixedMoment B node3879 node3879Labels := by rfl

def raw16969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16969 raw16969Labels = mixedMoment B node3568 node3568Labels := by
  calc
    mixedMoment B raw16969 raw16969Labels = mixedMoment B raw16969step0 raw16969step0Labels := by
      have ha : raw16969step0 = (fun i j => raw16969 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16969step0 raw16969; decide +kernel
      have hl : raw16969step0Labels = raw16969Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16969 raw16969Labels permutation514 permutation6
    _ = mixedMoment B node3568 node3568Labels := by rfl

def raw16970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16970 raw16970Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw16970 raw16970Labels = mixedMoment B raw16970step0 raw16970step0Labels := by
      have hz : ∀ j, raw16970 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16970step0 = (fun i j => raw16970 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16970step0 raw16970; decide +kernel
      have hl : raw16970step0Labels = raw16970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16970 raw16970Labels permutation520 hz
    mixedMoment B raw16970step0 raw16970step0Labels = mixedMoment B raw16970step1 raw16970step1Labels := by
      have ha : raw16970step1 = (fun i j => raw16970step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16970step1 raw16970step0; decide +kernel
      have hl : raw16970step1Labels = raw16970step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16970step0 raw16970step0Labels permutation122 permutation6
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw16971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16971 raw16971Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw16971 raw16971Labels = mixedMoment B raw16971step0 raw16971step0Labels := by
      have ha : raw16971step0 = (fun i j => raw16971 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16971step0 raw16971; decide +kernel
      have hl : raw16971step0Labels = raw16971Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16971 raw16971Labels permutation514 permutation6
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw16972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16972 raw16972Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw16972 raw16972Labels = mixedMoment B raw16972step0 raw16972step0Labels := by
      have ha : raw16972step0 = (fun i j => raw16972 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16972step0 raw16972; decide +kernel
      have hl : raw16972step0Labels = raw16972Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16972 raw16972Labels permutation152 permutation3
    _ = mixedMoment B node2567 node2567Labels := by rfl

def raw16973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16973 raw16973Labels = mixedMoment B node3923 node3923Labels := by
  calc
    mixedMoment B raw16973 raw16973Labels = mixedMoment B raw16973step0 raw16973step0Labels := by
      have ha : raw16973step0 = (fun i j => raw16973 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16973step0 raw16973; decide +kernel
      have hl : raw16973step0Labels = raw16973Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16973 raw16973Labels permutation152 permutation3
    _ = mixedMoment B node3923 node3923Labels := by rfl

def raw16974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw16974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16974 raw16974Labels = mixedMoment B node3969 node3969Labels := by
  calc
    mixedMoment B raw16974 raw16974Labels = mixedMoment B raw16974step0 raw16974step0Labels := by
      have ha : raw16974step0 = (fun i j => raw16974 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16974step0 raw16974; decide +kernel
      have hl : raw16974step0Labels = raw16974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16974 raw16974Labels permutation686 permutation3
    mixedMoment B raw16974step0 raw16974step0Labels = mixedMoment B raw16974step1 raw16974step1Labels := by
      have ha : raw16974step1 = -raw16974step0 := by apply Matrix.ext; change ∀ i j, raw16974step1 i j = -(raw16974step0 i j); unfold raw16974step1 raw16974step0; decide +kernel
      have hl : raw16974step1Labels = raw16974step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3969 node3969Labels := by rfl

def raw16975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16975 raw16975Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw16975 raw16975Labels = mixedMoment B raw16975step0 raw16975step0Labels := by
      have hz : ∀ j, raw16975 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16975step0 = (fun i j => raw16975 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16975step0 raw16975; decide +kernel
      have hl : raw16975step0Labels = raw16975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16975 raw16975Labels permutation520 hz
    mixedMoment B raw16975step0 raw16975step0Labels = mixedMoment B raw16975step1 raw16975step1Labels := by
      have ha : raw16975step1 = (fun i j => raw16975step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16975step1 raw16975step0; decide +kernel
      have hl : raw16975step1Labels = raw16975step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16975step0 raw16975step0Labels permutation32 permutation3
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw16976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16976 raw16976Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw16976 raw16976Labels = mixedMoment B raw16976step0 raw16976step0Labels := by
      have ha : raw16976step0 = (fun i j => raw16976 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16976step0 raw16976; decide +kernel
      have hl : raw16976step0Labels = raw16976Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16976 raw16976Labels permutation153 permutation3
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw16977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw16977step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16977 raw16977Labels = mixedMoment B node2533 node2533Labels := by
  calc
    mixedMoment B raw16977 raw16977Labels = mixedMoment B raw16977step0 raw16977step0Labels := by
      have ha : raw16977step0 = (fun i j => raw16977 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16977step0 raw16977; decide +kernel
      have hl : raw16977step0Labels = raw16977Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16977 raw16977Labels permutation159 permutation3
    _ = mixedMoment B node2533 node2533Labels := by rfl

def raw16978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw16978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16978 raw16978Labels = mixedMoment B node3680 node3680Labels := by
  calc
    mixedMoment B raw16978 raw16978Labels = mixedMoment B raw16978step0 raw16978step0Labels := by
      have ha : raw16978step0 = (fun i j => raw16978 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16978step0 raw16978; decide +kernel
      have hl : raw16978step0Labels = raw16978Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16978 raw16978Labels permutation583 permutation3
    mixedMoment B raw16978step0 raw16978step0Labels = mixedMoment B raw16978step1 raw16978step1Labels := by
      have ha : raw16978step1 = -raw16978step0 := by apply Matrix.ext; change ∀ i j, raw16978step1 i j = -(raw16978step0 i j); unfold raw16978step1 raw16978step0; decide +kernel
      have hl : raw16978step1Labels = raw16978step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3680 node3680Labels := by rfl

def raw16979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw16979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16979 raw16979Labels = mixedMoment B node3697 node3697Labels := by
  calc
    mixedMoment B raw16979 raw16979Labels = mixedMoment B raw16979step0 raw16979step0Labels := by
      have ha : raw16979step0 = (fun i j => raw16979 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16979step0 raw16979; decide +kernel
      have hl : raw16979step0Labels = raw16979Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16979 raw16979Labels permutation587 permutation3
    mixedMoment B raw16979step0 raw16979step0Labels = mixedMoment B raw16979step1 raw16979step1Labels := by
      have ha : raw16979step1 = -raw16979step0 := by apply Matrix.ext; change ∀ i j, raw16979step1 i j = -(raw16979step0 i j); unfold raw16979step1 raw16979step0; decide +kernel
      have hl : raw16979step1Labels = raw16979step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3697 node3697Labels := by rfl

def raw16980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16980 raw16980Labels = mixedMoment B node3574 node3574Labels := by
  calc
    mixedMoment B raw16980 raw16980Labels = mixedMoment B raw16980step0 raw16980step0Labels := by
      have ha : raw16980step0 = (fun i j => raw16980 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16980step0 raw16980; decide +kernel
      have hl : raw16980step0Labels = raw16980Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16980 raw16980Labels permutation514 permutation6
    _ = mixedMoment B node3574 node3574Labels := by rfl

def raw16981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw16981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw16981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16981 raw16981Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw16981 raw16981Labels = mixedMoment B raw16981step0 raw16981step0Labels := by
      have ha : raw16981step0 = (fun i j => raw16981 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16981step0 raw16981; decide +kernel
      have hl : raw16981step0Labels = raw16981Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16981 raw16981Labels permutation584 permutation3
    mixedMoment B raw16981step0 raw16981step0Labels = mixedMoment B raw16981step1 raw16981step1Labels := by
      have ha : raw16981step1 = -raw16981step0 := by apply Matrix.ext; change ∀ i j, raw16981step1 i j = -(raw16981step0 i j); unfold raw16981step1 raw16981step0; decide +kernel
      have hl : raw16981step1Labels = raw16981step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw16982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw16982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw16982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16982 raw16982Labels = mixedMoment B node2453 node2453Labels := by
  calc
    mixedMoment B raw16982 raw16982Labels = mixedMoment B raw16982step0 raw16982step0Labels := by
      have ha : raw16982step0 = (fun i j => raw16982 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16982step0 raw16982; decide +kernel
      have hl : raw16982step0Labels = raw16982Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16982 raw16982Labels permutation682 permutation3
    mixedMoment B raw16982step0 raw16982step0Labels = mixedMoment B raw16982step1 raw16982step1Labels := by
      have ha : raw16982step1 = -raw16982step0 := by apply Matrix.ext; change ∀ i j, raw16982step1 i j = -(raw16982step0 i j); unfold raw16982step1 raw16982step0; decide +kernel
      have hl : raw16982step1Labels = raw16982step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2453 node2453Labels := by rfl

def raw16983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw16983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16983 raw16983Labels = mixedMoment B node2456 node2456Labels := by
  calc
    mixedMoment B raw16983 raw16983Labels = mixedMoment B raw16983step0 raw16983step0Labels := by
      have ha : raw16983step0 = (fun i j => raw16983 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16983step0 raw16983; decide +kernel
      have hl : raw16983step0Labels = raw16983Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16983 raw16983Labels permutation681 permutation3
    mixedMoment B raw16983step0 raw16983step0Labels = mixedMoment B raw16983step1 raw16983step1Labels := by
      have ha : raw16983step1 = -raw16983step0 := by apply Matrix.ext; change ∀ i j, raw16983step1 i j = -(raw16983step0 i j); unfold raw16983step1 raw16983step0; decide +kernel
      have hl : raw16983step1Labels = raw16983step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2456 node2456Labels := by rfl

def raw16984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw16984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16984 raw16984Labels = mixedMoment B node2493 node2493Labels := by
  calc
    mixedMoment B raw16984 raw16984Labels = mixedMoment B raw16984step0 raw16984step0Labels := by
      have ha : raw16984step0 = (fun i j => raw16984 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16984step0 raw16984; decide +kernel
      have hl : raw16984step0Labels = raw16984Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16984 raw16984Labels permutation686 permutation3
    mixedMoment B raw16984step0 raw16984step0Labels = mixedMoment B raw16984step1 raw16984step1Labels := by
      have ha : raw16984step1 = -raw16984step0 := by apply Matrix.ext; change ∀ i j, raw16984step1 i j = -(raw16984step0 i j); unfold raw16984step1 raw16984step0; decide +kernel
      have hl : raw16984step1Labels = raw16984step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2493 node2493Labels := by rfl

def raw16985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw16985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16985 raw16985Labels = mixedMoment B node2460 node2460Labels := by
  calc
    mixedMoment B raw16985 raw16985Labels = mixedMoment B raw16985step0 raw16985step0Labels := by
      have ha : raw16985step0 = (fun i j => raw16985 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16985step0 raw16985; decide +kernel
      have hl : raw16985step0Labels = raw16985Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16985 raw16985Labels permutation680 permutation3
    mixedMoment B raw16985step0 raw16985step0Labels = mixedMoment B raw16985step1 raw16985step1Labels := by
      have ha : raw16985step1 = -raw16985step0 := by apply Matrix.ext; change ∀ i j, raw16985step1 i j = -(raw16985step0 i j); unfold raw16985step1 raw16985step0; decide +kernel
      have hl : raw16985step1Labels = raw16985step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2460 node2460Labels := by rfl

def raw16986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw16986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw16986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16986 raw16986Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw16986 raw16986Labels = mixedMoment B raw16986step0 raw16986step0Labels := by
      have hz : ∀ j, raw16986 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16986step0 = (fun i j => raw16986 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16986step0 raw16986; decide +kernel
      have hl : raw16986step0Labels = raw16986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16986 raw16986Labels permutation520 hz
    mixedMoment B raw16986step0 raw16986step0Labels = mixedMoment B raw16986step1 raw16986step1Labels := by
      have ha : raw16986step1 = (fun i j => raw16986step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16986step1 raw16986step0; decide +kernel
      have hl : raw16986step1Labels = raw16986step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16986step0 raw16986step0Labels permutation145 permutation3
    mixedMoment B raw16986step1 raw16986step1Labels = mixedMoment B raw16986step2 raw16986step2Labels := by
      have ha : raw16986step2 = -raw16986step1 := by apply Matrix.ext; change ∀ i j, raw16986step2 i j = -(raw16986step1 i j); unfold raw16986step2 raw16986step1; decide +kernel
      have hl : raw16986step2Labels = raw16986step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw16987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16987step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16987step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16987 raw16987Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw16987 raw16987Labels = mixedMoment B raw16987step0 raw16987step0Labels := by
      have ha : raw16987step0 = (fun i j => raw16987 (permutation451 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16987step0 raw16987; decide +kernel
      have hl : raw16987step0Labels = raw16987Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16987 raw16987Labels permutation451 permutation5
    mixedMoment B raw16987step0 raw16987step0Labels = mixedMoment B raw16987step1 raw16987step1Labels := by
      have ha : raw16987step1 = -raw16987step0 := by apply Matrix.ext; change ∀ i j, raw16987step1 i j = -(raw16987step0 i j); unfold raw16987step1 raw16987step0; decide +kernel
      have hl : raw16987step1Labels = raw16987step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16987step1 raw16987step1Labels = mixedMoment B raw16987step2 raw16987step2Labels := by
      have ha : raw16987step2 = raw16987step1 := by apply Matrix.ext; unfold raw16987step2 raw16987step1; decide +kernel
      have hl : raw16987step1Labels = labelEmbedding1 ∘ raw16987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16987step1 raw16987step1Labels raw16987step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw16988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw16988step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw16988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16988 raw16988Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw16988 raw16988Labels = mixedMoment B raw16988step0 raw16988step0Labels := by
      have ha : raw16988step0 = (fun i j => raw16988 (permutation514 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16988step0 raw16988; decide +kernel
      have hl : raw16988step0Labels = raw16988Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16988 raw16988Labels permutation514 permutation7
    mixedMoment B raw16988step0 raw16988step0Labels = mixedMoment B raw16988step1 raw16988step1Labels := by
      have ha : raw16988step1 = raw16988step0 := by apply Matrix.ext; unfold raw16988step1 raw16988step0; decide +kernel
      have hl : raw16988step0Labels = labelEmbedding1 ∘ raw16988step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16988step0 raw16988step0Labels raw16988step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw16989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16989step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16989step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16989 raw16989Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw16989 raw16989Labels = mixedMoment B raw16989step0 raw16989step0Labels := by
      have ha : raw16989step0 = (fun i j => raw16989 (permutation434 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16989step0 raw16989; decide +kernel
      have hl : raw16989step0Labels = raw16989Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16989 raw16989Labels permutation434 permutation5
    mixedMoment B raw16989step0 raw16989step0Labels = mixedMoment B raw16989step1 raw16989step1Labels := by
      have ha : raw16989step1 = -raw16989step0 := by apply Matrix.ext; change ∀ i j, raw16989step1 i j = -(raw16989step0 i j); unfold raw16989step1 raw16989step0; decide +kernel
      have hl : raw16989step1Labels = raw16989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16989step1 raw16989step1Labels = mixedMoment B raw16989step2 raw16989step2Labels := by
      have ha : raw16989step2 = raw16989step1 := by apply Matrix.ext; unfold raw16989step2 raw16989step1; decide +kernel
      have hl : raw16989step1Labels = labelEmbedding1 ∘ raw16989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16989step1 raw16989step1Labels raw16989step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw16990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16990 raw16990Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw16990 raw16990Labels = mixedMoment B raw16990step0 raw16990step0Labels := by
      have hz : ∀ j, raw16990 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16990step0 = (fun i j => raw16990 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16990step0 raw16990; decide +kernel
      have hl : raw16990step0Labels = raw16990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16990 raw16990Labels permutation520 hz
    mixedMoment B raw16990step0 raw16990step0Labels = mixedMoment B raw16990step1 raw16990step1Labels := by
      have ha : raw16990step1 = (fun i j => raw16990step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16990step1 raw16990step0; decide +kernel
      have hl : raw16990step1Labels = raw16990step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16990step0 raw16990step0Labels permutation126 permutation7
    mixedMoment B raw16990step1 raw16990step1Labels = mixedMoment B raw16990step2 raw16990step2Labels := by
      have ha : raw16990step2 = raw16990step1 := by apply Matrix.ext; unfold raw16990step2 raw16990step1; decide +kernel
      have hl : raw16990step1Labels = labelEmbedding1 ∘ raw16990step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16990step1 raw16990step1Labels raw16990step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw16991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16991step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16991 raw16991Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw16991 raw16991Labels = mixedMoment B raw16991step0 raw16991step0Labels := by
      have ha : raw16991step0 = (fun i j => raw16991 (permutation518 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16991step0 raw16991; decide +kernel
      have hl : raw16991step0Labels = raw16991Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16991 raw16991Labels permutation518 permutation7
    mixedMoment B raw16991step0 raw16991step0Labels = mixedMoment B raw16991step1 raw16991step1Labels := by
      have ha : raw16991step1 = raw16991step0 := by apply Matrix.ext; unfold raw16991step1 raw16991step0; decide +kernel
      have hl : raw16991step0Labels = labelEmbedding1 ∘ raw16991step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16991step0 raw16991step0Labels raw16991step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw16992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16992step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16992 raw16992Labels = mixedMoment B node3388 node3388Labels := by
  calc
    mixedMoment B raw16992 raw16992Labels = mixedMoment B raw16992step0 raw16992step0Labels := by
      have ha : raw16992step0 = (fun i j => raw16992 (permutation200 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16992step0 raw16992; decide +kernel
      have hl : raw16992step0Labels = raw16992Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16992 raw16992Labels permutation200 permutation5
    mixedMoment B raw16992step0 raw16992step0Labels = mixedMoment B raw16992step1 raw16992step1Labels := by
      have ha : raw16992step1 = -raw16992step0 := by apply Matrix.ext; change ∀ i j, raw16992step1 i j = -(raw16992step0 i j); unfold raw16992step1 raw16992step0; decide +kernel
      have hl : raw16992step1Labels = raw16992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16992step1 raw16992step1Labels = mixedMoment B raw16992step2 raw16992step2Labels := by
      have ha : raw16992step2 = raw16992step1 := by apply Matrix.ext; unfold raw16992step2 raw16992step1; decide +kernel
      have hl : raw16992step1Labels = labelEmbedding1 ∘ raw16992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16992step1 raw16992step1Labels raw16992step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3388 node3388Labels := by rfl

def raw16993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16993step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16993step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16993 raw16993Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw16993 raw16993Labels = mixedMoment B raw16993step0 raw16993step0Labels := by
      have ha : raw16993step0 = (fun i j => raw16993 (permutation440 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16993step0 raw16993; decide +kernel
      have hl : raw16993step0Labels = raw16993Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16993 raw16993Labels permutation440 permutation5
    mixedMoment B raw16993step0 raw16993step0Labels = mixedMoment B raw16993step1 raw16993step1Labels := by
      have ha : raw16993step1 = -raw16993step0 := by apply Matrix.ext; change ∀ i j, raw16993step1 i j = -(raw16993step0 i j); unfold raw16993step1 raw16993step0; decide +kernel
      have hl : raw16993step1Labels = raw16993step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16993step1 raw16993step1Labels = mixedMoment B raw16993step2 raw16993step2Labels := by
      have ha : raw16993step2 = raw16993step1 := by apply Matrix.ext; unfold raw16993step2 raw16993step1; decide +kernel
      have hl : raw16993step1Labels = labelEmbedding1 ∘ raw16993step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16993step1 raw16993step1Labels raw16993step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw16994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16994step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16994step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16994step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16994 raw16994Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw16994 raw16994Labels = mixedMoment B raw16994step0 raw16994step0Labels := by
      have ha : raw16994step0 = (fun i j => raw16994 (permutation434 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16994step0 raw16994; decide +kernel
      have hl : raw16994step0Labels = raw16994Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16994 raw16994Labels permutation434 permutation5
    mixedMoment B raw16994step0 raw16994step0Labels = mixedMoment B raw16994step1 raw16994step1Labels := by
      have ha : raw16994step1 = -raw16994step0 := by apply Matrix.ext; change ∀ i j, raw16994step1 i j = -(raw16994step0 i j); unfold raw16994step1 raw16994step0; decide +kernel
      have hl : raw16994step1Labels = raw16994step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16994step1 raw16994step1Labels = mixedMoment B raw16994step2 raw16994step2Labels := by
      have ha : raw16994step2 = raw16994step1 := by apply Matrix.ext; unfold raw16994step2 raw16994step1; decide +kernel
      have hl : raw16994step1Labels = labelEmbedding1 ∘ raw16994step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16994step1 raw16994step1Labels raw16994step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2878 node2878Labels := by rfl

def raw16995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16995 raw16995Labels = mixedMoment B node4028 node4028Labels := by
  calc
    mixedMoment B raw16995 raw16995Labels = mixedMoment B raw16995step0 raw16995step0Labels := by
      have hz : ∀ j, raw16995 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16995step0 = (fun i j => raw16995 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16995step0 raw16995; decide +kernel
      have hl : raw16995step0Labels = raw16995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16995 raw16995Labels permutation520 hz
    mixedMoment B raw16995step0 raw16995step0Labels = mixedMoment B raw16995step1 raw16995step1Labels := by
      have ha : raw16995step1 = (fun i j => raw16995step0 (permutation104 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16995step1 raw16995step0; decide +kernel
      have hl : raw16995step1Labels = raw16995step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16995step0 raw16995step0Labels permutation104 permutation5
    mixedMoment B raw16995step1 raw16995step1Labels = mixedMoment B raw16995step2 raw16995step2Labels := by
      have ha : raw16995step2 = -raw16995step1 := by apply Matrix.ext; change ∀ i j, raw16995step2 i j = -(raw16995step1 i j); unfold raw16995step2 raw16995step1; decide +kernel
      have hl : raw16995step2Labels = raw16995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16995step2 raw16995step2Labels = mixedMoment B raw16995step3 raw16995step3Labels := by
      have ha : raw16995step3 = raw16995step2 := by apply Matrix.ext; unfold raw16995step3 raw16995step2; decide +kernel
      have hl : raw16995step2Labels = labelEmbedding1 ∘ raw16995step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16995step2 raw16995step2Labels raw16995step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4028 node4028Labels := by rfl

def raw16996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16996step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16996step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16996step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16996 raw16996Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw16996 raw16996Labels = mixedMoment B raw16996step0 raw16996step0Labels := by
      have ha : raw16996step0 = (fun i j => raw16996 (permutation448 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16996step0 raw16996; decide +kernel
      have hl : raw16996step0Labels = raw16996Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16996 raw16996Labels permutation448 permutation5
    mixedMoment B raw16996step0 raw16996step0Labels = mixedMoment B raw16996step1 raw16996step1Labels := by
      have ha : raw16996step1 = -raw16996step0 := by apply Matrix.ext; change ∀ i j, raw16996step1 i j = -(raw16996step0 i j); unfold raw16996step1 raw16996step0; decide +kernel
      have hl : raw16996step1Labels = raw16996step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16996step1 raw16996step1Labels = mixedMoment B raw16996step2 raw16996step2Labels := by
      have ha : raw16996step2 = raw16996step1 := by apply Matrix.ext; unfold raw16996step2 raw16996step1; decide +kernel
      have hl : raw16996step1Labels = labelEmbedding1 ∘ raw16996step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16996step1 raw16996step1Labels raw16996step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw16997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16997step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16997step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16997 raw16997Labels = mixedMoment B node3371 node3371Labels := by
  calc
    mixedMoment B raw16997 raw16997Labels = mixedMoment B raw16997step0 raw16997step0Labels := by
      have ha : raw16997step0 = (fun i j => raw16997 (permutation203 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16997step0 raw16997; decide +kernel
      have hl : raw16997step0Labels = raw16997Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16997 raw16997Labels permutation203 permutation5
    mixedMoment B raw16997step0 raw16997step0Labels = mixedMoment B raw16997step1 raw16997step1Labels := by
      have ha : raw16997step1 = -raw16997step0 := by apply Matrix.ext; change ∀ i j, raw16997step1 i j = -(raw16997step0 i j); unfold raw16997step1 raw16997step0; decide +kernel
      have hl : raw16997step1Labels = raw16997step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16997step1 raw16997step1Labels = mixedMoment B raw16997step2 raw16997step2Labels := by
      have ha : raw16997step2 = raw16997step1 := by apply Matrix.ext; unfold raw16997step2 raw16997step1; decide +kernel
      have hl : raw16997step1Labels = labelEmbedding1 ∘ raw16997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16997step1 raw16997step1Labels raw16997step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3371 node3371Labels := by rfl

def raw16998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16998step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16998 raw16998Labels = mixedMoment B node3943 node3943Labels := by
  calc
    mixedMoment B raw16998 raw16998Labels = mixedMoment B raw16998step0 raw16998step0Labels := by
      have ha : raw16998step0 = (fun i j => raw16998 (permutation428 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16998step0 raw16998; decide +kernel
      have hl : raw16998step0Labels = raw16998Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16998 raw16998Labels permutation428 permutation5
    mixedMoment B raw16998step0 raw16998step0Labels = mixedMoment B raw16998step1 raw16998step1Labels := by
      have ha : raw16998step1 = raw16998step0 := by apply Matrix.ext; unfold raw16998step1 raw16998step0; decide +kernel
      have hl : raw16998step0Labels = labelEmbedding1 ∘ raw16998step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16998step0 raw16998step0Labels raw16998step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3943 node3943Labels := by rfl

def raw16999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16999step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16999step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16999 raw16999Labels = mixedMoment B node2854 node2854Labels := by
  calc
    mixedMoment B raw16999 raw16999Labels = mixedMoment B raw16999step0 raw16999step0Labels := by
      have ha : raw16999step0 = (fun i j => raw16999 (permutation437 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16999step0 raw16999; decide +kernel
      have hl : raw16999step0Labels = raw16999Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16999 raw16999Labels permutation437 permutation5
    mixedMoment B raw16999step0 raw16999step0Labels = mixedMoment B raw16999step1 raw16999step1Labels := by
      have ha : raw16999step1 = -raw16999step0 := by apply Matrix.ext; change ∀ i j, raw16999step1 i j = -(raw16999step0 i j); unfold raw16999step1 raw16999step0; decide +kernel
      have hl : raw16999step1Labels = raw16999step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16999step1 raw16999step1Labels = mixedMoment B raw16999step2 raw16999step2Labels := by
      have ha : raw16999step2 = raw16999step1 := by apply Matrix.ext; unfold raw16999step2 raw16999step1; decide +kernel
      have hl : raw16999step1Labels = labelEmbedding1 ∘ raw16999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16999step1 raw16999step1Labels raw16999step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2854 node2854Labels := by rfl

def raw17000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw17000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17000 raw17000Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw17000 raw17000Labels = mixedMoment B raw17000step0 raw17000step0Labels := by
      have hz : ∀ j, raw17000 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17000step0 = (fun i j => raw17000 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17000step0 raw17000; decide +kernel
      have hl : raw17000step0Labels = raw17000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17000 raw17000Labels permutation520 hz
    mixedMoment B raw17000step0 raw17000step0Labels = mixedMoment B raw17000step1 raw17000step1Labels := by
      have ha : raw17000step1 = (fun i j => raw17000step0 (permutation100 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17000step1 raw17000step0; decide +kernel
      have hl : raw17000step1Labels = raw17000step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17000step0 raw17000step0Labels permutation100 permutation5
    mixedMoment B raw17000step1 raw17000step1Labels = mixedMoment B raw17000step2 raw17000step2Labels := by
      have ha : raw17000step2 = raw17000step1 := by apply Matrix.ext; unfold raw17000step2 raw17000step1; decide +kernel
      have hl : raw17000step1Labels = labelEmbedding1 ∘ raw17000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17000step1 raw17000step1Labels raw17000step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw17001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw17001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17001step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17001 raw17001Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw17001 raw17001Labels = mixedMoment B raw17001step0 raw17001step0Labels := by
      have ha : raw17001step0 = (fun i j => raw17001 (permutation411 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17001step0 raw17001; decide +kernel
      have hl : raw17001step0Labels = raw17001Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17001 raw17001Labels permutation411 permutation5
    mixedMoment B raw17001step0 raw17001step0Labels = mixedMoment B raw17001step1 raw17001step1Labels := by
      have ha : raw17001step1 = raw17001step0 := by apply Matrix.ext; unfold raw17001step1 raw17001step0; decide +kernel
      have hl : raw17001step0Labels = labelEmbedding1 ∘ raw17001step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17001step0 raw17001step0Labels raw17001step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw17002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17002step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17002step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17002 raw17002Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw17002 raw17002Labels = mixedMoment B raw17002step0 raw17002step0Labels := by
      have ha : raw17002step0 = (fun i j => raw17002 (permutation200 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17002step0 raw17002; decide +kernel
      have hl : raw17002step0Labels = raw17002Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17002 raw17002Labels permutation200 permutation5
    mixedMoment B raw17002step0 raw17002step0Labels = mixedMoment B raw17002step1 raw17002step1Labels := by
      have ha : raw17002step1 = -raw17002step0 := by apply Matrix.ext; change ∀ i j, raw17002step1 i j = -(raw17002step0 i j); unfold raw17002step1 raw17002step0; decide +kernel
      have hl : raw17002step1Labels = raw17002step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17002step1 raw17002step1Labels = mixedMoment B raw17002step2 raw17002step2Labels := by
      have ha : raw17002step2 = raw17002step1 := by apply Matrix.ext; unfold raw17002step2 raw17002step1; decide +kernel
      have hl : raw17002step1Labels = labelEmbedding1 ∘ raw17002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17002step1 raw17002step1Labels raw17002step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw17003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17003step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17003 raw17003Labels = mixedMoment B node3951 node3951Labels := by
  calc
    mixedMoment B raw17003 raw17003Labels = mixedMoment B raw17003step0 raw17003step0Labels := by
      have ha : raw17003step0 = (fun i j => raw17003 (permutation518 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17003step0 raw17003; decide +kernel
      have hl : raw17003step0Labels = raw17003Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17003 raw17003Labels permutation518 permutation7
    mixedMoment B raw17003step0 raw17003step0Labels = mixedMoment B raw17003step1 raw17003step1Labels := by
      have ha : raw17003step1 = raw17003step0 := by apply Matrix.ext; unfold raw17003step1 raw17003step0; decide +kernel
      have hl : raw17003step0Labels = labelEmbedding1 ∘ raw17003step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17003step0 raw17003step0Labels raw17003step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3951 node3951Labels := by rfl

def raw17004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17004 raw17004Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw17004 raw17004Labels = mixedMoment B raw17004step0 raw17004step0Labels := by
      have ha : raw17004step0 = (fun i j => raw17004 (permutation517 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17004step0 raw17004; decide +kernel
      have hl : raw17004step0Labels = raw17004Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17004 raw17004Labels permutation517 permutation7
    mixedMoment B raw17004step0 raw17004step0Labels = mixedMoment B raw17004step1 raw17004step1Labels := by
      have ha : raw17004step1 = raw17004step0 := by apply Matrix.ext; unfold raw17004step1 raw17004step0; decide +kernel
      have hl : raw17004step0Labels = labelEmbedding1 ∘ raw17004step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17004step0 raw17004step0Labels raw17004step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

def raw17005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw17005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17005step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17005 raw17005Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw17005 raw17005Labels = mixedMoment B raw17005step0 raw17005step0Labels := by
      have hz : ∀ j, raw17005 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17005step0 = (fun i j => raw17005 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17005step0 raw17005; decide +kernel
      have hl : raw17005step0Labels = raw17005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17005 raw17005Labels permutation520 hz
    mixedMoment B raw17005step0 raw17005step0Labels = mixedMoment B raw17005step1 raw17005step1Labels := by
      have ha : raw17005step1 = (fun i j => raw17005step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17005step1 raw17005step0; decide +kernel
      have hl : raw17005step1Labels = raw17005step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17005step0 raw17005step0Labels permutation127 permutation7
    mixedMoment B raw17005step1 raw17005step1Labels = mixedMoment B raw17005step2 raw17005step2Labels := by
      have ha : raw17005step2 = raw17005step1 := by apply Matrix.ext; unfold raw17005step2 raw17005step1; decide +kernel
      have hl : raw17005step1Labels = labelEmbedding1 ∘ raw17005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17005step1 raw17005step1Labels raw17005step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw17006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw17006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17006step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17006 raw17006Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw17006 raw17006Labels = mixedMoment B raw17006step0 raw17006step0Labels := by
      have ha : raw17006step0 = (fun i j => raw17006 (permutation519 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17006step0 raw17006; decide +kernel
      have hl : raw17006step0Labels = raw17006Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17006 raw17006Labels permutation519 permutation7
    mixedMoment B raw17006step0 raw17006step0Labels = mixedMoment B raw17006step1 raw17006step1Labels := by
      have ha : raw17006step1 = raw17006step0 := by apply Matrix.ext; unfold raw17006step1 raw17006step0; decide +kernel
      have hl : raw17006step0Labels = labelEmbedding1 ∘ raw17006step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17006step0 raw17006step0Labels raw17006step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw17007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw17007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw17007step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17007step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17007 raw17007Labels = mixedMoment B node3369 node3369Labels := by
  calc
    mixedMoment B raw17007 raw17007Labels = mixedMoment B raw17007step0 raw17007step0Labels := by
      have ha : raw17007step0 = (fun i j => raw17007 (permutation201 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17007step0 raw17007; decide +kernel
      have hl : raw17007step0Labels = raw17007Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17007 raw17007Labels permutation201 permutation5
    mixedMoment B raw17007step0 raw17007step0Labels = mixedMoment B raw17007step1 raw17007step1Labels := by
      have ha : raw17007step1 = -raw17007step0 := by apply Matrix.ext; change ∀ i j, raw17007step1 i j = -(raw17007step0 i j); unfold raw17007step1 raw17007step0; decide +kernel
      have hl : raw17007step1Labels = raw17007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17007step1 raw17007step1Labels = mixedMoment B raw17007step2 raw17007step2Labels := by
      have ha : raw17007step2 = raw17007step1 := by apply Matrix.ext; unfold raw17007step2 raw17007step1; decide +kernel
      have hl : raw17007step1Labels = labelEmbedding1 ∘ raw17007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17007step1 raw17007step1Labels raw17007step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3369 node3369Labels := by rfl

def raw17008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw17008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw17008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw17008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17008 raw17008Labels = mixedMoment B node3747 node3747Labels := by
  calc
    mixedMoment B raw17008 raw17008Labels = mixedMoment B raw17008step0 raw17008step0Labels := by
      have ha : raw17008step0 = (fun i j => raw17008 (permutation580 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17008step0 raw17008; decide +kernel
      have hl : raw17008step0Labels = raw17008Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17008 raw17008Labels permutation580 permutation5
    mixedMoment B raw17008step0 raw17008step0Labels = mixedMoment B raw17008step1 raw17008step1Labels := by
      have ha : raw17008step1 = raw17008step0 := by apply Matrix.ext; unfold raw17008step1 raw17008step0; decide +kernel
      have hl : raw17008step0Labels = labelEmbedding1 ∘ raw17008step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17008step0 raw17008step0Labels raw17008step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3747 node3747Labels := by rfl

def raw17009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw17009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17009step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17009step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17009 raw17009Labels = mixedMoment B node3759 node3759Labels := by
  calc
    mixedMoment B raw17009 raw17009Labels = mixedMoment B raw17009step0 raw17009step0Labels := by
      have ha : raw17009step0 = (fun i j => raw17009 (permutation576 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17009step0 raw17009; decide +kernel
      have hl : raw17009step0Labels = raw17009Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17009 raw17009Labels permutation576 permutation5
    mixedMoment B raw17009step0 raw17009step0Labels = mixedMoment B raw17009step1 raw17009step1Labels := by
      have ha : raw17009step1 = raw17009step0 := by apply Matrix.ext; unfold raw17009step1 raw17009step0; decide +kernel
      have hl : raw17009step0Labels = labelEmbedding1 ∘ raw17009step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17009step0 raw17009step0Labels raw17009step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3759 node3759Labels := by rfl

def raw17010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw17010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw17010step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17010step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17010 raw17010Labels = mixedMoment B node2852 node2852Labels := by
  calc
    mixedMoment B raw17010 raw17010Labels = mixedMoment B raw17010step0 raw17010step0Labels := by
      have ha : raw17010step0 = (fun i j => raw17010 (permutation435 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17010step0 raw17010; decide +kernel
      have hl : raw17010step0Labels = raw17010Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17010 raw17010Labels permutation435 permutation5
    mixedMoment B raw17010step0 raw17010step0Labels = mixedMoment B raw17010step1 raw17010step1Labels := by
      have ha : raw17010step1 = -raw17010step0 := by apply Matrix.ext; change ∀ i j, raw17010step1 i j = -(raw17010step0 i j); unfold raw17010step1 raw17010step0; decide +kernel
      have hl : raw17010step1Labels = raw17010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17010step1 raw17010step1Labels = mixedMoment B raw17010step2 raw17010step2Labels := by
      have ha : raw17010step2 = raw17010step1 := by apply Matrix.ext; unfold raw17010step2 raw17010step1; decide +kernel
      have hl : raw17010step1Labels = labelEmbedding1 ∘ raw17010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17010step1 raw17010step1Labels raw17010step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2852 node2852Labels := by rfl

def raw17011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw17011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17011step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17011 raw17011Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw17011 raw17011Labels = mixedMoment B raw17011step0 raw17011step0Labels := by
      have ha : raw17011step0 = (fun i j => raw17011 (permutation549 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17011step0 raw17011; decide +kernel
      have hl : raw17011step0Labels = raw17011Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17011 raw17011Labels permutation549 permutation5
    mixedMoment B raw17011step0 raw17011step0Labels = mixedMoment B raw17011step1 raw17011step1Labels := by
      have ha : raw17011step1 = raw17011step0 := by apply Matrix.ext; unfold raw17011step1 raw17011step0; decide +kernel
      have hl : raw17011step0Labels = labelEmbedding1 ∘ raw17011step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17011step0 raw17011step0Labels raw17011step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw17012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw17012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw17012step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw17012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17012step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw17012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17012 raw17012Labels = mixedMoment B node3368 node3368Labels := by
  calc
    mixedMoment B raw17012 raw17012Labels = mixedMoment B raw17012step0 raw17012step0Labels := by
      have ha : raw17012step0 = (fun i j => raw17012 (permutation200 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17012step0 raw17012; decide +kernel
      have hl : raw17012step0Labels = raw17012Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17012 raw17012Labels permutation200 permutation5
    mixedMoment B raw17012step0 raw17012step0Labels = mixedMoment B raw17012step1 raw17012step1Labels := by
      have ha : raw17012step1 = -raw17012step0 := by apply Matrix.ext; change ∀ i j, raw17012step1 i j = -(raw17012step0 i j); unfold raw17012step1 raw17012step0; decide +kernel
      have hl : raw17012step1Labels = raw17012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17012step1 raw17012step1Labels = mixedMoment B raw17012step2 raw17012step2Labels := by
      have ha : raw17012step2 = raw17012step1 := by apply Matrix.ext; unfold raw17012step2 raw17012step1; decide +kernel
      have hl : raw17012step1Labels = labelEmbedding1 ∘ raw17012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17012step1 raw17012step1Labels raw17012step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3368 node3368Labels := by rfl

def raw17013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw17013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw17013step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw17013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17013 raw17013Labels = mixedMoment B node3438 node3438Labels := by
  calc
    mixedMoment B raw17013 raw17013Labels = mixedMoment B raw17013step0 raw17013step0Labels := by
      have ha : raw17013step0 = (fun i j => raw17013 (permutation677 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17013step0 raw17013; decide +kernel
      have hl : raw17013step0Labels = raw17013Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17013 raw17013Labels permutation677 permutation5
    mixedMoment B raw17013step0 raw17013step0Labels = mixedMoment B raw17013step1 raw17013step1Labels := by
      have ha : raw17013step1 = raw17013step0 := by apply Matrix.ext; unfold raw17013step1 raw17013step0; decide +kernel
      have hl : raw17013step0Labels = labelEmbedding1 ∘ raw17013step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17013step0 raw17013step0Labels raw17013step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3438 node3438Labels := by rfl

def raw17014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw17014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17014step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17014 raw17014Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw17014 raw17014Labels = mixedMoment B raw17014step0 raw17014step0Labels := by
      have ha : raw17014step0 = (fun i j => raw17014 (permutation673 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17014step0 raw17014; decide +kernel
      have hl : raw17014step0Labels = raw17014Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17014 raw17014Labels permutation673 permutation5
    mixedMoment B raw17014step0 raw17014step0Labels = mixedMoment B raw17014step1 raw17014step1Labels := by
      have ha : raw17014step1 = raw17014step0 := by apply Matrix.ext; unfold raw17014step1 raw17014step0; decide +kernel
      have hl : raw17014step0Labels = labelEmbedding1 ∘ raw17014step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17014step0 raw17014step0Labels raw17014step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw17015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw17015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw17015step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw17015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17015step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw17015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17015 raw17015Labels = mixedMoment B node2851 node2851Labels := by
  calc
    mixedMoment B raw17015 raw17015Labels = mixedMoment B raw17015step0 raw17015step0Labels := by
      have ha : raw17015step0 = (fun i j => raw17015 (permutation434 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17015step0 raw17015; decide +kernel
      have hl : raw17015step0Labels = raw17015Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17015 raw17015Labels permutation434 permutation5
    mixedMoment B raw17015step0 raw17015step0Labels = mixedMoment B raw17015step1 raw17015step1Labels := by
      have ha : raw17015step1 = -raw17015step0 := by apply Matrix.ext; change ∀ i j, raw17015step1 i j = -(raw17015step0 i j); unfold raw17015step1 raw17015step0; decide +kernel
      have hl : raw17015step1Labels = raw17015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17015step1 raw17015step1Labels = mixedMoment B raw17015step2 raw17015step2Labels := by
      have ha : raw17015step2 = raw17015step1 := by apply Matrix.ext; unfold raw17015step2 raw17015step1; decide +kernel
      have hl : raw17015step1Labels = labelEmbedding1 ∘ raw17015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17015step1 raw17015step1Labels raw17015step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2851 node2851Labels := by rfl

def raw17016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw17016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17016 raw17016Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw17016 raw17016Labels = mixedMoment B raw17016step0 raw17016step0Labels := by
      have hz : ∀ j, raw17016 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17016step0 = (fun i j => raw17016 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17016step0 raw17016; decide +kernel
      have hl : raw17016step0Labels = raw17016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17016 raw17016Labels permutation520 hz
    mixedMoment B raw17016step0 raw17016step0Labels = mixedMoment B raw17016step1 raw17016step1Labels := by
      have ha : raw17016step1 = (fun i j => raw17016step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17016step1 raw17016step0; decide +kernel
      have hl : raw17016step1Labels = raw17016step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17016step0 raw17016step0Labels permutation142 permutation5
    mixedMoment B raw17016step1 raw17016step1Labels = mixedMoment B raw17016step2 raw17016step2Labels := by
      have ha : raw17016step2 = raw17016step1 := by apply Matrix.ext; unfold raw17016step2 raw17016step1; decide +kernel
      have hl : raw17016step1Labels = labelEmbedding1 ∘ raw17016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17016step1 raw17016step1Labels raw17016step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw17017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17017step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17017 raw17017Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw17017 raw17017Labels = mixedMoment B raw17017step0 raw17017step0Labels := by
      have ha : raw17017step0 = (fun i j => raw17017 (permutation439 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17017step0 raw17017; decide +kernel
      have hl : raw17017step0Labels = raw17017Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17017 raw17017Labels permutation439 permutation4
    mixedMoment B raw17017step0 raw17017step0Labels = mixedMoment B raw17017step1 raw17017step1Labels := by
      have ha : raw17017step1 = -raw17017step0 := by apply Matrix.ext; change ∀ i j, raw17017step1 i j = -(raw17017step0 i j); unfold raw17017step1 raw17017step0; decide +kernel
      have hl : raw17017step1Labels = raw17017step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw17018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17018 raw17018Labels = mixedMoment B node3068 node3068Labels := by
  calc
    _ = mixedMoment B node3068 node3068Labels := by rfl

def raw17019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw17019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17019 raw17019Labels = mixedMoment B node2944 node2944Labels := by
  calc
    mixedMoment B raw17019 raw17019Labels = mixedMoment B raw17019step0 raw17019step0Labels := by
      have ha : raw17019step0 = (fun i j => raw17019 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17019step0 raw17019; decide +kernel
      have hl : raw17019step0Labels = raw17019Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17019 raw17019Labels permutation158 permutation2
    _ = mixedMoment B node2944 node2944Labels := by rfl

def raw17020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17020 raw17020Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw17020 raw17020Labels = mixedMoment B raw17020step0 raw17020step0Labels := by
      have ha : raw17020step0 = (fun i j => raw17020 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17020step0 raw17020; decide +kernel
      have hl : raw17020step0Labels = raw17020Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17020 raw17020Labels permutation154 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

def raw17021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw17021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17021 raw17021Labels = mixedMoment B node2920 node2920Labels := by
  calc
    _ = mixedMoment B node2920 node2920Labels := by rfl

def raw17022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw17022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17022 raw17022Labels = mixedMoment B node2918 node2918Labels := by
  calc
    _ = mixedMoment B node2918 node2918Labels := by rfl

def raw17023 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]
def raw17023Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17023step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw17023step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17023step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw17023step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17023step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw17023step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical17023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17023 raw17023Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw17023 raw17023Labels = mixedMoment B raw17023step0 raw17023step0Labels := by
      have hz : ∀ j, raw17023 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17023step0 = (fun i j => raw17023 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17023step0 raw17023; decide +kernel
      have hl : raw17023step0Labels = raw17023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17023 raw17023Labels permutation520 hz
    mixedMoment B raw17023step0 raw17023step0Labels = mixedMoment B raw17023step1 raw17023step1Labels := by
      have ha : raw17023step1 = (fun i j => raw17023step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw17023step1 raw17023step0; decide +kernel
      have hl : raw17023step1Labels = raw17023step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17023step0 raw17023step0Labels permutation122 permutation0
    mixedMoment B raw17023step1 raw17023step1Labels = mixedMoment B raw17023step2 raw17023step2Labels := by
      have ha : raw17023step2 = -raw17023step1 := by apply Matrix.ext; change ∀ i j, raw17023step2 i j = -(raw17023step1 i j); unfold raw17023step2 raw17023step1; decide +kernel
      have hl : raw17023step2Labels = raw17023step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
