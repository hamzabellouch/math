import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
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

def raw9472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9472 raw9472Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw9472 raw9472Labels = mixedMoment B raw9472step0 raw9472step0Labels := by
      have hz : ∀ j, raw9472 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9472step0 = (fun i j => raw9472 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9472step0 raw9472; decide +kernel
      have hl : raw9472step0Labels = raw9472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9472 raw9472Labels permutation265 hz
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw9473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9473step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9473 raw9473Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw9473 raw9473Labels = mixedMoment B raw9473step0 raw9473step0Labels := by
      have hz : ∀ j, raw9473 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9473step0 = (fun i j => raw9473 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9473step0 raw9473; decide +kernel
      have hl : raw9473step0Labels = raw9473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9473 raw9473Labels permutation265 hz
    mixedMoment B raw9473step0 raw9473step0Labels = mixedMoment B raw9473step1 raw9473step1Labels := by
      have ha : raw9473step1 = (fun i j => raw9473step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9473step1 raw9473step0; decide +kernel
      have hl : raw9473step1Labels = raw9473step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9473step0 raw9473step0Labels permutation151 permutation2
    mixedMoment B raw9473step1 raw9473step1Labels = mixedMoment B raw9473step2 raw9473step2Labels := by
      have ha : raw9473step2 = -raw9473step1 := by apply Matrix.ext; change ∀ i j, raw9473step2 i j = -(raw9473step1 i j); unfold raw9473step2 raw9473step1; decide +kernel
      have hl : raw9473step2Labels = raw9473step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw9474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9474 raw9474Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw9474 raw9474Labels = mixedMoment B raw9474step0 raw9474step0Labels := by
      have hz : ∀ j, raw9474 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9474step0 = (fun i j => raw9474 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9474step0 raw9474; decide +kernel
      have hl : raw9474step0Labels = raw9474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9474 raw9474Labels permutation265 hz
    mixedMoment B raw9474step0 raw9474step0Labels = mixedMoment B raw9474step1 raw9474step1Labels := by
      have ha : raw9474step1 = (fun i j => raw9474step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9474step1 raw9474step0; decide +kernel
      have hl : raw9474step1Labels = raw9474step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9474step0 raw9474step0Labels permutation38 permutation2
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw9475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9475 raw9475Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw9475 raw9475Labels = mixedMoment B raw9475step0 raw9475step0Labels := by
      have hz : ∀ j, raw9475 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9475step0 = (fun i j => raw9475 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9475step0 raw9475; decide +kernel
      have hl : raw9475step0Labels = raw9475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9475 raw9475Labels permutation265 hz
    mixedMoment B raw9475step0 raw9475step0Labels = mixedMoment B raw9475step1 raw9475step1Labels := by
      have ha : raw9475step1 = (fun i j => raw9475step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9475step1 raw9475step0; decide +kernel
      have hl : raw9475step1Labels = raw9475step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9475step0 raw9475step0Labels permutation33 permutation2
    _ = mixedMoment B node3079 node3079Labels := by rfl

def raw9476 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9476step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9476step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9476 raw9476Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw9476 raw9476Labels = mixedMoment B raw9476step0 raw9476step0Labels := by
      have hz : ∀ j, raw9476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9476step0 = (fun i j => raw9476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9476step0 raw9476; decide +kernel
      have hl : raw9476step0Labels = raw9476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9476 raw9476Labels permutation434 hz
    mixedMoment B raw9476step0 raw9476step0Labels = mixedMoment B raw9476step1 raw9476step1Labels := by
      have hz : ∀ j, raw9476step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9476step1 = (fun i j => raw9476step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9476step1 raw9476step0; decide +kernel
      have hl : raw9476step1Labels = raw9476step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9476step0 raw9476step0Labels permutation56 hz
    mixedMoment B raw9476step1 raw9476step1Labels = mixedMoment B raw9476step2 raw9476step2Labels := by
      have ha : raw9476step2 = (fun i j => raw9476step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9476step2 raw9476step1; decide +kernel
      have hl : raw9476step2Labels = raw9476step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9476step1 raw9476step1Labels permutation31 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw9477 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9477 raw9477Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw9477 raw9477Labels = mixedMoment B raw9477step0 raw9477step0Labels := by
      have hz : ∀ j, raw9477 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9477step0 = (fun i j => raw9477 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9477step0 raw9477; decide +kernel
      have hl : raw9477step0Labels = raw9477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9477 raw9477Labels permutation265 hz
    mixedMoment B raw9477step0 raw9477step0Labels = mixedMoment B raw9477step1 raw9477step1Labels := by
      have ha : raw9477step1 = (fun i j => raw9477step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9477step1 raw9477step0; decide +kernel
      have hl : raw9477step1Labels = raw9477step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9477step0 raw9477step0Labels permutation149 permutation2
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw9478 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9478 raw9478Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw9478 raw9478Labels = mixedMoment B raw9478step0 raw9478step0Labels := by
      have hz : ∀ j, raw9478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9478step0 = (fun i j => raw9478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9478step0 raw9478; decide +kernel
      have hl : raw9478step0Labels = raw9478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9478 raw9478Labels permutation434 hz
    mixedMoment B raw9478step0 raw9478step0Labels = mixedMoment B raw9478step1 raw9478step1Labels := by
      have ha : raw9478step1 = (fun i j => raw9478step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9478step1 raw9478step0; decide +kernel
      have hl : raw9478step1Labels = raw9478step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9478step0 raw9478step0Labels permutation149 permutation2
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw9479 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9479 raw9479Labels = mixedMoment B node4598 node4598Labels := by
  calc
    mixedMoment B raw9479 raw9479Labels = mixedMoment B raw9479step0 raw9479step0Labels := by
      have ha : raw9479step0 = (fun i j => raw9479 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9479step0 raw9479; decide +kernel
      have hl : raw9479step0Labels = raw9479Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9479 raw9479Labels permutation674 permutation2
    _ = mixedMoment B node4598 node4598Labels := by rfl

def raw9480 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw9480step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9480step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9480step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9480step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9480 raw9480Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw9480 raw9480Labels = mixedMoment B raw9480step0 raw9480step0Labels := by
      have hz : ∀ j, raw9480 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9480step0 = (fun i j => raw9480 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9480step0 raw9480; decide +kernel
      have hl : raw9480step0Labels = raw9480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9480 raw9480Labels permutation265 hz
    mixedMoment B raw9480step0 raw9480step0Labels = mixedMoment B raw9480step1 raw9480step1Labels := by
      have ha : raw9480step1 = (fun i j => raw9480step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9480step1 raw9480step0; decide +kernel
      have hl : raw9480step1Labels = raw9480step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9480step0 raw9480step0Labels permutation53 permutation4
    mixedMoment B raw9480step1 raw9480step1Labels = mixedMoment B raw9480step2 raw9480step2Labels := by
      have ha : raw9480step2 = -raw9480step1 := by apply Matrix.ext; change ∀ i j, raw9480step2 i j = -(raw9480step1 i j); unfold raw9480step2 raw9480step1; decide +kernel
      have hl : raw9480step2Labels = raw9480step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9480step2 raw9480step2Labels = mixedMoment B raw9480step3 raw9480step3Labels := by
      have ha : raw9480step3 = raw9480step2 := by apply Matrix.ext; unfold raw9480step3 raw9480step2; decide +kernel
      have hl : raw9480step2Labels = labelEmbedding7 ∘ raw9480step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9480step2 raw9480step2Labels raw9480step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw9481 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9481step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9481 raw9481Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw9481 raw9481Labels = mixedMoment B raw9481step0 raw9481step0Labels := by
      have hz : ∀ j, raw9481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9481step0 = (fun i j => raw9481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9481step0 raw9481; decide +kernel
      have hl : raw9481step0Labels = raw9481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9481 raw9481Labels permutation434 hz
    mixedMoment B raw9481step0 raw9481step0Labels = mixedMoment B raw9481step1 raw9481step1Labels := by
      have hz : ∀ j, raw9481step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9481step1 = (fun i j => raw9481step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9481step1 raw9481step0; decide +kernel
      have hl : raw9481step1Labels = raw9481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9481step0 raw9481step0Labels permutation56 hz
    mixedMoment B raw9481step1 raw9481step1Labels = mixedMoment B raw9481step2 raw9481step2Labels := by
      have ha : raw9481step2 = (fun i j => raw9481step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9481step2 raw9481step1; decide +kernel
      have hl : raw9481step2Labels = raw9481step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9481step1 raw9481step1Labels permutation30 permutation2
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw9482 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw9482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9482 raw9482Labels = mixedMoment B node4604 node4604Labels := by
  calc
    mixedMoment B raw9482 raw9482Labels = mixedMoment B raw9482step0 raw9482step0Labels := by
      have hz : ∀ j, raw9482 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9482step0 = (fun i j => raw9482 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9482step0 raw9482; decide +kernel
      have hl : raw9482step0Labels = raw9482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9482 raw9482Labels permutation265 hz
    mixedMoment B raw9482step0 raw9482step0Labels = mixedMoment B raw9482step1 raw9482step1Labels := by
      have ha : raw9482step1 = (fun i j => raw9482step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9482step1 raw9482step0; decide +kernel
      have hl : raw9482step1Labels = raw9482step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9482step0 raw9482step0Labels permutation150 permutation2
    _ = mixedMoment B node4604 node4604Labels := by rfl

def raw9483 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw9483step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9483step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9483step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9483step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9483 raw9483Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw9483 raw9483Labels = mixedMoment B raw9483step0 raw9483step0Labels := by
      have hz : ∀ j, raw9483 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9483step0 = (fun i j => raw9483 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9483step0 raw9483; decide +kernel
      have hl : raw9483step0Labels = raw9483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9483 raw9483Labels permutation265 hz
    mixedMoment B raw9483step0 raw9483step0Labels = mixedMoment B raw9483step1 raw9483step1Labels := by
      have ha : raw9483step1 = (fun i j => raw9483step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9483step1 raw9483step0; decide +kernel
      have hl : raw9483step1Labels = raw9483step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9483step0 raw9483step0Labels permutation51 permutation4
    mixedMoment B raw9483step1 raw9483step1Labels = mixedMoment B raw9483step2 raw9483step2Labels := by
      have ha : raw9483step2 = -raw9483step1 := by apply Matrix.ext; change ∀ i j, raw9483step2 i j = -(raw9483step1 i j); unfold raw9483step2 raw9483step1; decide +kernel
      have hl : raw9483step2Labels = raw9483step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9483step2 raw9483step2Labels = mixedMoment B raw9483step3 raw9483step3Labels := by
      have ha : raw9483step3 = raw9483step2 := by apply Matrix.ext; unfold raw9483step3 raw9483step2; decide +kernel
      have hl : raw9483step2Labels = labelEmbedding7 ∘ raw9483step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9483step2 raw9483step2Labels raw9483step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw9484 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw9484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9484 raw9484Labels = mixedMoment B node4604 node4604Labels := by
  calc
    mixedMoment B raw9484 raw9484Labels = mixedMoment B raw9484step0 raw9484step0Labels := by
      have hz : ∀ j, raw9484 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9484step0 = (fun i j => raw9484 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9484step0 raw9484; decide +kernel
      have hl : raw9484step0Labels = raw9484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9484 raw9484Labels permutation265 hz
    mixedMoment B raw9484step0 raw9484step0Labels = mixedMoment B raw9484step1 raw9484step1Labels := by
      have ha : raw9484step1 = (fun i j => raw9484step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9484step1 raw9484step0; decide +kernel
      have hl : raw9484step1Labels = raw9484step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9484step0 raw9484step0Labels permutation148 permutation2
    _ = mixedMoment B node4604 node4604Labels := by rfl

def raw9485 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9485step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9485step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9485 raw9485Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw9485 raw9485Labels = mixedMoment B raw9485step0 raw9485step0Labels := by
      have hz : ∀ j, raw9485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9485step0 = (fun i j => raw9485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9485step0 raw9485; decide +kernel
      have hl : raw9485step0Labels = raw9485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9485 raw9485Labels permutation434 hz
    mixedMoment B raw9485step0 raw9485step0Labels = mixedMoment B raw9485step1 raw9485step1Labels := by
      have hz : ∀ j, raw9485step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9485step1 = (fun i j => raw9485step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9485step1 raw9485step0; decide +kernel
      have hl : raw9485step1Labels = raw9485step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9485step0 raw9485step0Labels permutation56 hz
    mixedMoment B raw9485step1 raw9485step1Labels = mixedMoment B raw9485step2 raw9485step2Labels := by
      have ha : raw9485step2 = (fun i j => raw9485step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9485step2 raw9485step1; decide +kernel
      have hl : raw9485step2Labels = raw9485step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9485step1 raw9485step1Labels permutation31 permutation3
    _ = mixedMoment B node3113 node3113Labels := by rfl

def raw9486 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9486 raw9486Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw9486 raw9486Labels = mixedMoment B raw9486step0 raw9486step0Labels := by
      have hz : ∀ j, raw9486 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9486step0 = (fun i j => raw9486 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9486step0 raw9486; decide +kernel
      have hl : raw9486step0Labels = raw9486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9486 raw9486Labels permutation265 hz
    mixedMoment B raw9486step0 raw9486step0Labels = mixedMoment B raw9486step1 raw9486step1Labels := by
      have ha : raw9486step1 = (fun i j => raw9486step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9486step1 raw9486step0; decide +kernel
      have hl : raw9486step1Labels = raw9486step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9486step0 raw9486step0Labels permutation149 permutation3
    _ = mixedMoment B node1270 node1270Labels := by rfl

def raw9487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9487 raw9487Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw9487 raw9487Labels = mixedMoment B raw9487step0 raw9487step0Labels := by
      have hz : ∀ j, raw9487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9487step0 = (fun i j => raw9487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9487step0 raw9487; decide +kernel
      have hl : raw9487step0Labels = raw9487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9487 raw9487Labels permutation434 hz
    mixedMoment B raw9487step0 raw9487step0Labels = mixedMoment B raw9487step1 raw9487step1Labels := by
      have ha : raw9487step1 = (fun i j => raw9487step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9487step1 raw9487step0; decide +kernel
      have hl : raw9487step1Labels = raw9487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9487step0 raw9487step0Labels permutation32 permutation6
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw9488 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9488 raw9488Labels = mixedMoment B node1256 node1256Labels := by
  calc
    mixedMoment B raw9488 raw9488Labels = mixedMoment B raw9488step0 raw9488step0Labels := by
      have ha : raw9488step0 = (fun i j => raw9488 (permutation665 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9488step0 raw9488; decide +kernel
      have hl : raw9488step0Labels = raw9488Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9488 raw9488Labels permutation665 permutation3
    _ = mixedMoment B node1256 node1256Labels := by rfl

def raw9489 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw9489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9489 raw9489Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw9489 raw9489Labels = mixedMoment B raw9489step0 raw9489step0Labels := by
      have hz : ∀ j, raw9489 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9489step0 = (fun i j => raw9489 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9489step0 raw9489; decide +kernel
      have hl : raw9489step0Labels = raw9489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9489 raw9489Labels permutation265 hz
    mixedMoment B raw9489step0 raw9489step0Labels = mixedMoment B raw9489step1 raw9489step1Labels := by
      have ha : raw9489step1 = (fun i j => raw9489step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9489step1 raw9489step0; decide +kernel
      have hl : raw9489step1Labels = raw9489step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9489step0 raw9489step0Labels permutation38 permutation6
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw9490 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw9490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9490 raw9490Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw9490 raw9490Labels = mixedMoment B raw9490step0 raw9490step0Labels := by
      have hz : ∀ j, raw9490 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9490step0 = (fun i j => raw9490 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9490step0 raw9490; decide +kernel
      have hl : raw9490step0Labels = raw9490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9490 raw9490Labels permutation434 hz
    mixedMoment B raw9490step0 raw9490step0Labels = mixedMoment B raw9490step1 raw9490step1Labels := by
      have hz : ∀ j, raw9490step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9490step1 = (fun i j => raw9490step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9490step1 raw9490step0; decide +kernel
      have hl : raw9490step1Labels = raw9490step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9490step0 raw9490step0Labels permutation56 hz
    mixedMoment B raw9490step1 raw9490step1Labels = mixedMoment B raw9490step2 raw9490step2Labels := by
      have ha : raw9490step2 = (fun i j => raw9490step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9490step2 raw9490step1; decide +kernel
      have hl : raw9490step2Labels = raw9490step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9490step1 raw9490step1Labels permutation8 permutation6
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw9491 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw9491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9491 raw9491Labels = mixedMoment B node1257 node1257Labels := by
  calc
    mixedMoment B raw9491 raw9491Labels = mixedMoment B raw9491step0 raw9491step0Labels := by
      have hz : ∀ j, raw9491 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9491step0 = (fun i j => raw9491 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9491step0 raw9491; decide +kernel
      have hl : raw9491step0Labels = raw9491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9491 raw9491Labels permutation265 hz
    mixedMoment B raw9491step0 raw9491step0Labels = mixedMoment B raw9491step1 raw9491step1Labels := by
      have ha : raw9491step1 = (fun i j => raw9491step0 (permutation147 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9491step1 raw9491step0; decide +kernel
      have hl : raw9491step1Labels = raw9491step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9491step0 raw9491step0Labels permutation147 permutation3
    _ = mixedMoment B node1257 node1257Labels := by rfl

def raw9492 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw9492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9492 raw9492Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw9492 raw9492Labels = mixedMoment B raw9492step0 raw9492step0Labels := by
      have hz : ∀ j, raw9492 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9492step0 = (fun i j => raw9492 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9492step0 raw9492; decide +kernel
      have hl : raw9492step0Labels = raw9492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9492 raw9492Labels permutation265 hz
    mixedMoment B raw9492step0 raw9492step0Labels = mixedMoment B raw9492step1 raw9492step1Labels := by
      have ha : raw9492step1 = (fun i j => raw9492step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9492step1 raw9492step0; decide +kernel
      have hl : raw9492step1Labels = raw9492step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9492step0 raw9492step0Labels permutation32 permutation6
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw9493 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw9493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9493 raw9493Labels = mixedMoment B node1257 node1257Labels := by
  calc
    mixedMoment B raw9493 raw9493Labels = mixedMoment B raw9493step0 raw9493step0Labels := by
      have hz : ∀ j, raw9493 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9493step0 = (fun i j => raw9493 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9493step0 raw9493; decide +kernel
      have hl : raw9493step0Labels = raw9493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9493 raw9493Labels permutation265 hz
    mixedMoment B raw9493step0 raw9493step0Labels = mixedMoment B raw9493step1 raw9493step1Labels := by
      have ha : raw9493step1 = (fun i j => raw9493step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9493step1 raw9493step0; decide +kernel
      have hl : raw9493step1Labels = raw9493step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9493step0 raw9493step0Labels permutation146 permutation3
    _ = mixedMoment B node1257 node1257Labels := by rfl

def raw9494 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9494step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9494step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9494step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9494step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9494step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9494 raw9494Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw9494 raw9494Labels = mixedMoment B raw9494step0 raw9494step0Labels := by
      have hz : ∀ j, raw9494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9494step0 = (fun i j => raw9494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9494step0 raw9494; decide +kernel
      have hl : raw9494step0Labels = raw9494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9494 raw9494Labels permutation434 hz
    mixedMoment B raw9494step0 raw9494step0Labels = mixedMoment B raw9494step1 raw9494step1Labels := by
      have hz : ∀ j, raw9494step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9494step1 = (fun i j => raw9494step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9494step1 raw9494step0; decide +kernel
      have hl : raw9494step1Labels = raw9494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9494step0 raw9494step0Labels permutation56 hz
    mixedMoment B raw9494step1 raw9494step1Labels = mixedMoment B raw9494step2 raw9494step2Labels := by
      have ha : raw9494step2 = (fun i j => raw9494step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9494step2 raw9494step1; decide +kernel
      have hl : raw9494step2Labels = raw9494step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9494step1 raw9494step1Labels permutation8 permutation7
    mixedMoment B raw9494step2 raw9494step2Labels = mixedMoment B raw9494step3 raw9494step3Labels := by
      have ha : raw9494step3 = raw9494step2 := by apply Matrix.ext; unfold raw9494step3 raw9494step2; decide +kernel
      have hl : raw9494step2Labels = labelEmbedding1 ∘ raw9494step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9494step2 raw9494step2Labels raw9494step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw9495 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9495step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9495 raw9495Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw9495 raw9495Labels = mixedMoment B raw9495step0 raw9495step0Labels := by
      have hz : ∀ j, raw9495 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9495step0 = (fun i j => raw9495 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9495step0 raw9495; decide +kernel
      have hl : raw9495step0Labels = raw9495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9495 raw9495Labels permutation265 hz
    mixedMoment B raw9495step0 raw9495step0Labels = mixedMoment B raw9495step1 raw9495step1Labels := by
      have ha : raw9495step1 = (fun i j => raw9495step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9495step1 raw9495step0; decide +kernel
      have hl : raw9495step1Labels = raw9495step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9495step0 raw9495step0Labels permutation32 permutation7
    mixedMoment B raw9495step1 raw9495step1Labels = mixedMoment B raw9495step2 raw9495step2Labels := by
      have ha : raw9495step2 = raw9495step1 := by apply Matrix.ext; unfold raw9495step2 raw9495step1; decide +kernel
      have hl : raw9495step1Labels = labelEmbedding1 ∘ raw9495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9495step1 raw9495step1Labels raw9495step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw9496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9496step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9496 raw9496Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw9496 raw9496Labels = mixedMoment B raw9496step0 raw9496step0Labels := by
      have hz : ∀ j, raw9496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9496step0 = (fun i j => raw9496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9496step0 raw9496; decide +kernel
      have hl : raw9496step0Labels = raw9496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9496 raw9496Labels permutation434 hz
    mixedMoment B raw9496step0 raw9496step0Labels = mixedMoment B raw9496step1 raw9496step1Labels := by
      have ha : raw9496step1 = (fun i j => raw9496step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9496step1 raw9496step0; decide +kernel
      have hl : raw9496step1Labels = raw9496step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9496step0 raw9496step0Labels permutation32 permutation7
    mixedMoment B raw9496step1 raw9496step1Labels = mixedMoment B raw9496step2 raw9496step2Labels := by
      have ha : raw9496step2 = raw9496step1 := by apply Matrix.ext; unfold raw9496step2 raw9496step1; decide +kernel
      have hl : raw9496step1Labels = labelEmbedding1 ∘ raw9496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9496step1 raw9496step1Labels raw9496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw9497 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9497step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9497 raw9497Labels = mixedMoment B node3057 node3057Labels := by
  calc
    mixedMoment B raw9497 raw9497Labels = mixedMoment B raw9497step0 raw9497step0Labels := by
      have ha : raw9497step0 = (fun i j => raw9497 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9497step0 raw9497; decide +kernel
      have hl : raw9497step0Labels = raw9497Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9497 raw9497Labels permutation152 permutation7
    mixedMoment B raw9497step0 raw9497step0Labels = mixedMoment B raw9497step1 raw9497step1Labels := by
      have ha : raw9497step1 = raw9497step0 := by apply Matrix.ext; unfold raw9497step1 raw9497step0; decide +kernel
      have hl : raw9497step0Labels = labelEmbedding1 ∘ raw9497step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9497step0 raw9497step0Labels raw9497step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3057 node3057Labels := by rfl

def raw9498 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9498step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9498step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9498step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9498step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9498 raw9498Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw9498 raw9498Labels = mixedMoment B raw9498step0 raw9498step0Labels := by
      have hz : ∀ j, raw9498 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9498step0 = (fun i j => raw9498 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9498step0 raw9498; decide +kernel
      have hl : raw9498step0Labels = raw9498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9498 raw9498Labels permutation265 hz
    mixedMoment B raw9498step0 raw9498step0Labels = mixedMoment B raw9498step1 raw9498step1Labels := by
      have ha : raw9498step1 = (fun i j => raw9498step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9498step1 raw9498step0; decide +kernel
      have hl : raw9498step1Labels = raw9498step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9498step0 raw9498step0Labels permutation55 permutation5
    mixedMoment B raw9498step1 raw9498step1Labels = mixedMoment B raw9498step2 raw9498step2Labels := by
      have ha : raw9498step2 = -raw9498step1 := by apply Matrix.ext; change ∀ i j, raw9498step2 i j = -(raw9498step1 i j); unfold raw9498step2 raw9498step1; decide +kernel
      have hl : raw9498step2Labels = raw9498step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9498step2 raw9498step2Labels = mixedMoment B raw9498step3 raw9498step3Labels := by
      have ha : raw9498step3 = raw9498step2 := by apply Matrix.ext; unfold raw9498step3 raw9498step2; decide +kernel
      have hl : raw9498step2Labels = labelEmbedding1 ∘ raw9498step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9498step2 raw9498step2Labels raw9498step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3156 node3156Labels := by rfl

def raw9499 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9499step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw9499step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9499step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw9499step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9499 raw9499Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw9499 raw9499Labels = mixedMoment B raw9499step0 raw9499step0Labels := by
      have hz : ∀ j, raw9499 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9499step0 = (fun i j => raw9499 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9499step0 raw9499; decide +kernel
      have hl : raw9499step0Labels = raw9499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9499 raw9499Labels permutation434 hz
    mixedMoment B raw9499step0 raw9499step0Labels = mixedMoment B raw9499step1 raw9499step1Labels := by
      have hz : ∀ j, raw9499step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9499step1 = (fun i j => raw9499step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9499step1 raw9499step0; decide +kernel
      have hl : raw9499step1Labels = raw9499step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9499step0 raw9499step0Labels permutation56 hz
    mixedMoment B raw9499step1 raw9499step1Labels = mixedMoment B raw9499step2 raw9499step2Labels := by
      have ha : raw9499step2 = (fun i j => raw9499step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9499step2 raw9499step1; decide +kernel
      have hl : raw9499step2Labels = raw9499step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9499step1 raw9499step1Labels permutation8 permutation7
    mixedMoment B raw9499step2 raw9499step2Labels = mixedMoment B raw9499step3 raw9499step3Labels := by
      have ha : raw9499step3 = raw9499step2 := by apply Matrix.ext; unfold raw9499step3 raw9499step2; decide +kernel
      have hl : raw9499step2Labels = labelEmbedding1 ∘ raw9499step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9499step2 raw9499step2Labels raw9499step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw9500 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9500step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9500 raw9500Labels = mixedMoment B node3022 node3022Labels := by
  calc
    mixedMoment B raw9500 raw9500Labels = mixedMoment B raw9500step0 raw9500step0Labels := by
      have hz : ∀ j, raw9500 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9500step0 = (fun i j => raw9500 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9500step0 raw9500; decide +kernel
      have hl : raw9500step0Labels = raw9500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9500 raw9500Labels permutation265 hz
    mixedMoment B raw9500step0 raw9500step0Labels = mixedMoment B raw9500step1 raw9500step1Labels := by
      have ha : raw9500step1 = (fun i j => raw9500step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9500step1 raw9500step0; decide +kernel
      have hl : raw9500step1Labels = raw9500step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9500step0 raw9500step0Labels permutation32 permutation7
    mixedMoment B raw9500step1 raw9500step1Labels = mixedMoment B raw9500step2 raw9500step2Labels := by
      have ha : raw9500step2 = raw9500step1 := by apply Matrix.ext; unfold raw9500step2 raw9500step1; decide +kernel
      have hl : raw9500step1Labels = labelEmbedding1 ∘ raw9500step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9500step1 raw9500step1Labels raw9500step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3022 node3022Labels := by rfl

def raw9501 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9501step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9501step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9501step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9501step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9501 raw9501Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw9501 raw9501Labels = mixedMoment B raw9501step0 raw9501step0Labels := by
      have hz : ∀ j, raw9501 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9501step0 = (fun i j => raw9501 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9501step0 raw9501; decide +kernel
      have hl : raw9501step0Labels = raw9501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9501 raw9501Labels permutation265 hz
    mixedMoment B raw9501step0 raw9501step0Labels = mixedMoment B raw9501step1 raw9501step1Labels := by
      have ha : raw9501step1 = (fun i j => raw9501step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9501step1 raw9501step0; decide +kernel
      have hl : raw9501step1Labels = raw9501step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9501step0 raw9501step0Labels permutation54 permutation5
    mixedMoment B raw9501step1 raw9501step1Labels = mixedMoment B raw9501step2 raw9501step2Labels := by
      have ha : raw9501step2 = -raw9501step1 := by apply Matrix.ext; change ∀ i j, raw9501step2 i j = -(raw9501step1 i j); unfold raw9501step2 raw9501step1; decide +kernel
      have hl : raw9501step2Labels = raw9501step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9501step2 raw9501step2Labels = mixedMoment B raw9501step3 raw9501step3Labels := by
      have ha : raw9501step3 = raw9501step2 := by apply Matrix.ext; unfold raw9501step3 raw9501step2; decide +kernel
      have hl : raw9501step2Labels = labelEmbedding1 ∘ raw9501step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9501step2 raw9501step2Labels raw9501step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3156 node3156Labels := by rfl

def raw9502 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9502step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9502 raw9502Labels = mixedMoment B node3022 node3022Labels := by
  calc
    mixedMoment B raw9502 raw9502Labels = mixedMoment B raw9502step0 raw9502step0Labels := by
      have hz : ∀ j, raw9502 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9502step0 = (fun i j => raw9502 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9502step0 raw9502; decide +kernel
      have hl : raw9502step0Labels = raw9502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9502 raw9502Labels permutation265 hz
    mixedMoment B raw9502step0 raw9502step0Labels = mixedMoment B raw9502step1 raw9502step1Labels := by
      have ha : raw9502step1 = (fun i j => raw9502step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9502step1 raw9502step0; decide +kernel
      have hl : raw9502step1Labels = raw9502step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9502step0 raw9502step0Labels permutation38 permutation7
    mixedMoment B raw9502step1 raw9502step1Labels = mixedMoment B raw9502step2 raw9502step2Labels := by
      have ha : raw9502step2 = raw9502step1 := by apply Matrix.ext; unfold raw9502step2 raw9502step1; decide +kernel
      have hl : raw9502step1Labels = labelEmbedding1 ∘ raw9502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9502step1 raw9502step1Labels raw9502step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3022 node3022Labels := by rfl

def raw9503 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9503 raw9503Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw9503 raw9503Labels = mixedMoment B raw9503step0 raw9503step0Labels := by
      have hz : ∀ j, raw9503 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9503step0 = (fun i j => raw9503 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9503step0 raw9503; decide +kernel
      have hl : raw9503step0Labels = raw9503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9503 raw9503Labels permutation434 hz
    mixedMoment B raw9503step0 raw9503step0Labels = mixedMoment B raw9503step1 raw9503step1Labels := by
      have hz : ∀ j, raw9503step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9503step1 = (fun i j => raw9503step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9503step1 raw9503step0; decide +kernel
      have hl : raw9503step1Labels = raw9503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9503step0 raw9503step0Labels permutation56 hz
    mixedMoment B raw9503step1 raw9503step1Labels = mixedMoment B raw9503step2 raw9503step2Labels := by
      have ha : raw9503step2 = (fun i j => raw9503step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9503step2 raw9503step1; decide +kernel
      have hl : raw9503step2Labels = raw9503step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9503step1 raw9503step1Labels permutation31 permutation2
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw9504 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9504 raw9504Labels = mixedMoment B node1234 node1234Labels := by
  calc
    mixedMoment B raw9504 raw9504Labels = mixedMoment B raw9504step0 raw9504step0Labels := by
      have hz : ∀ j, raw9504 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9504step0 = (fun i j => raw9504 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9504step0 raw9504; decide +kernel
      have hl : raw9504step0Labels = raw9504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9504 raw9504Labels permutation265 hz
    mixedMoment B raw9504step0 raw9504step0Labels = mixedMoment B raw9504step1 raw9504step1Labels := by
      have ha : raw9504step1 = (fun i j => raw9504step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9504step1 raw9504step0; decide +kernel
      have hl : raw9504step1Labels = raw9504step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9504step0 raw9504step0Labels permutation149 permutation2
    _ = mixedMoment B node1234 node1234Labels := by rfl

def raw9505 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw9505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9505 raw9505Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw9505 raw9505Labels = mixedMoment B raw9505step0 raw9505step0Labels := by
      have hz : ∀ j, raw9505 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9505step0 = (fun i j => raw9505 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9505step0 raw9505; decide +kernel
      have hl : raw9505step0Labels = raw9505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9505 raw9505Labels permutation265 hz
    mixedMoment B raw9505step0 raw9505step0Labels = mixedMoment B raw9505step1 raw9505step1Labels := by
      have ha : raw9505step1 = (fun i j => raw9505step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9505step1 raw9505step0; decide +kernel
      have hl : raw9505step1Labels = raw9505step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9505step0 raw9505step0Labels permutation53 permutation4
    mixedMoment B raw9505step1 raw9505step1Labels = mixedMoment B raw9505step2 raw9505step2Labels := by
      have ha : raw9505step2 = -raw9505step1 := by apply Matrix.ext; change ∀ i j, raw9505step2 i j = -(raw9505step1 i j); unfold raw9505step2 raw9505step1; decide +kernel
      have hl : raw9505step2Labels = raw9505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2133 node2133Labels := by rfl

def raw9506 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw9506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9506 raw9506Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw9506 raw9506Labels = mixedMoment B raw9506step0 raw9506step0Labels := by
      have hz : ∀ j, raw9506 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9506step0 = (fun i j => raw9506 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9506step0 raw9506; decide +kernel
      have hl : raw9506step0Labels = raw9506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9506 raw9506Labels permutation265 hz
    mixedMoment B raw9506step0 raw9506step0Labels = mixedMoment B raw9506step1 raw9506step1Labels := by
      have ha : raw9506step1 = (fun i j => raw9506step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9506step1 raw9506step0; decide +kernel
      have hl : raw9506step1Labels = raw9506step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9506step0 raw9506step0Labels permutation51 permutation4
    mixedMoment B raw9506step1 raw9506step1Labels = mixedMoment B raw9506step2 raw9506step2Labels := by
      have ha : raw9506step2 = -raw9506step1 := by apply Matrix.ext; change ∀ i j, raw9506step2 i j = -(raw9506step1 i j); unfold raw9506step2 raw9506step1; decide +kernel
      have hl : raw9506step2Labels = raw9506step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2133 node2133Labels := by rfl

def raw9507 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9507 raw9507Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw9507 raw9507Labels = mixedMoment B raw9507step0 raw9507step0Labels := by
      have hz : ∀ j, raw9507 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9507step0 = (fun i j => raw9507 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9507step0 raw9507; decide +kernel
      have hl : raw9507step0Labels = raw9507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9507 raw9507Labels permutation434 hz
    mixedMoment B raw9507step0 raw9507step0Labels = mixedMoment B raw9507step1 raw9507step1Labels := by
      have ha : raw9507step1 = (fun i j => raw9507step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9507step1 raw9507step0; decide +kernel
      have hl : raw9507step1Labels = raw9507step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9507step0 raw9507step0Labels permutation149 permutation2
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw9508 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9508 raw9508Labels = mixedMoment B node1232 node1232Labels := by
  calc
    mixedMoment B raw9508 raw9508Labels = mixedMoment B raw9508step0 raw9508step0Labels := by
      have ha : raw9508step0 = (fun i j => raw9508 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9508step0 raw9508; decide +kernel
      have hl : raw9508step0Labels = raw9508Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9508 raw9508Labels permutation674 permutation2
    _ = mixedMoment B node1232 node1232Labels := by rfl

def raw9509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9509 raw9509Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw9509 raw9509Labels = mixedMoment B raw9509step0 raw9509step0Labels := by
      have hz : ∀ j, raw9509 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9509step0 = (fun i j => raw9509 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9509step0 raw9509; decide +kernel
      have hl : raw9509step0Labels = raw9509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9509 raw9509Labels permutation434 hz
    mixedMoment B raw9509step0 raw9509step0Labels = mixedMoment B raw9509step1 raw9509step1Labels := by
      have hz : ∀ j, raw9509step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9509step1 = (fun i j => raw9509step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9509step1 raw9509step0; decide +kernel
      have hl : raw9509step1Labels = raw9509step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9509step0 raw9509step0Labels permutation80 hz
    _ = mixedMoment B node5449 node5449Labels := by rfl

def raw9510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9510 raw9510Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw9510 raw9510Labels = mixedMoment B raw9510step0 raw9510step0Labels := by
      have hz : ∀ j, raw9510 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9510step0 = (fun i j => raw9510 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9510step0 raw9510; decide +kernel
      have hl : raw9510step0Labels = raw9510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9510 raw9510Labels permutation434 hz
    mixedMoment B raw9510step0 raw9510step0Labels = mixedMoment B raw9510step1 raw9510step1Labels := by
      have ha : raw9510step1 = (fun i j => raw9510step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9510step1 raw9510step0; decide +kernel
      have hl : raw9510step1Labels = raw9510step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9510step0 raw9510step0Labels permutation38 permutation2
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw9511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9511 raw9511Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw9511 raw9511Labels = mixedMoment B raw9511step0 raw9511step0Labels := by
      have hz : ∀ j, raw9511 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9511step0 = (fun i j => raw9511 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9511step0 raw9511; decide +kernel
      have hl : raw9511step0Labels = raw9511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9511 raw9511Labels permutation346 hz
    mixedMoment B raw9511step0 raw9511step0Labels = mixedMoment B raw9511step1 raw9511step1Labels := by
      have ha : raw9511step1 = (fun i j => raw9511step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9511step1 raw9511step0; decide +kernel
      have hl : raw9511step1Labels = raw9511step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9511step0 raw9511step0Labels permutation38 permutation2
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw9512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9512step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9512step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9512step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9512step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9512step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9512step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9512 raw9512Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw9512 raw9512Labels = mixedMoment B raw9512step0 raw9512step0Labels := by
      have hz : ∀ j, raw9512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9512step0 = (fun i j => raw9512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9512step0 raw9512; decide +kernel
      have hl : raw9512step0Labels = raw9512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9512 raw9512Labels permutation434 hz
    mixedMoment B raw9512step0 raw9512step0Labels = mixedMoment B raw9512step1 raw9512step1Labels := by
      have hz : ∀ j, raw9512step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9512step1 = (fun i j => raw9512step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9512step1 raw9512step0; decide +kernel
      have hl : raw9512step1Labels = raw9512step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9512step0 raw9512step0Labels permutation80 hz
    mixedMoment B raw9512step1 raw9512step1Labels = mixedMoment B raw9512step2 raw9512step2Labels := by
      have ha : raw9512step2 = (fun i j => raw9512step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9512step2 raw9512step1; decide +kernel
      have hl : raw9512step2Labels = raw9512step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9512step1 raw9512step1Labels permutation10 permutation7
    mixedMoment B raw9512step2 raw9512step2Labels = mixedMoment B raw9512step3 raw9512step3Labels := by
      have ha : raw9512step3 = -raw9512step2 := by apply Matrix.ext; change ∀ i j, raw9512step3 i j = -(raw9512step2 i j); unfold raw9512step3 raw9512step2; decide +kernel
      have hl : raw9512step3Labels = raw9512step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9512step3 raw9512step3Labels = mixedMoment B raw9512step4 raw9512step4Labels := by
      have ha : raw9512step4 = raw9512step3 := by apply Matrix.ext; unfold raw9512step4 raw9512step3; decide +kernel
      have hl : raw9512step3Labels = labelEmbedding10 ∘ raw9512step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9512step3 raw9512step3Labels raw9512step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw9513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9513step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9513step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9513 raw9513Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw9513 raw9513Labels = mixedMoment B raw9513step0 raw9513step0Labels := by
      have hz : ∀ j, raw9513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9513step0 = (fun i j => raw9513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9513step0 raw9513; decide +kernel
      have hl : raw9513step0Labels = raw9513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9513 raw9513Labels permutation434 hz
    mixedMoment B raw9513step0 raw9513step0Labels = mixedMoment B raw9513step1 raw9513step1Labels := by
      have hz : ∀ j, raw9513step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9513step1 = (fun i j => raw9513step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9513step1 raw9513step0; decide +kernel
      have hl : raw9513step1Labels = raw9513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9513step0 raw9513step0Labels permutation80 hz
    mixedMoment B raw9513step1 raw9513step1Labels = mixedMoment B raw9513step2 raw9513step2Labels := by
      have ha : raw9513step2 = (fun i j => raw9513step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9513step2 raw9513step1; decide +kernel
      have hl : raw9513step2Labels = raw9513step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9513step1 raw9513step1Labels permutation10 permutation2
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw9514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9514 raw9514Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw9514 raw9514Labels = mixedMoment B raw9514step0 raw9514step0Labels := by
      have hz : ∀ j, raw9514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9514step0 = (fun i j => raw9514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9514step0 raw9514; decide +kernel
      have hl : raw9514step0Labels = raw9514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9514 raw9514Labels permutation434 hz
    mixedMoment B raw9514step0 raw9514step0Labels = mixedMoment B raw9514step1 raw9514step1Labels := by
      have ha : raw9514step1 = (fun i j => raw9514step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9514step1 raw9514step0; decide +kernel
      have hl : raw9514step1Labels = raw9514step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9514step0 raw9514step0Labels permutation40 permutation2
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw9515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9515 raw9515Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw9515 raw9515Labels = mixedMoment B raw9515step0 raw9515step0Labels := by
      have hz : ∀ j, raw9515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9515step0 = (fun i j => raw9515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9515step0 raw9515; decide +kernel
      have hl : raw9515step0Labels = raw9515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9515 raw9515Labels permutation346 hz
    mixedMoment B raw9515step0 raw9515step0Labels = mixedMoment B raw9515step1 raw9515step1Labels := by
      have ha : raw9515step1 = (fun i j => raw9515step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9515step1 raw9515step0; decide +kernel
      have hl : raw9515step1Labels = raw9515step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9515step0 raw9515step0Labels permutation40 permutation2
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw9516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9516step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9516 raw9516Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw9516 raw9516Labels = mixedMoment B raw9516step0 raw9516step0Labels := by
      have hz : ∀ j, raw9516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9516step0 = (fun i j => raw9516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9516step0 raw9516; decide +kernel
      have hl : raw9516step0Labels = raw9516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9516 raw9516Labels permutation434 hz
    mixedMoment B raw9516step0 raw9516step0Labels = mixedMoment B raw9516step1 raw9516step1Labels := by
      have hz : ∀ j, raw9516step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9516step1 = (fun i j => raw9516step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9516step1 raw9516step0; decide +kernel
      have hl : raw9516step1Labels = raw9516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9516step0 raw9516step0Labels permutation80 hz
    mixedMoment B raw9516step1 raw9516step1Labels = mixedMoment B raw9516step2 raw9516step2Labels := by
      have ha : raw9516step2 = (fun i j => raw9516step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9516step2 raw9516step1; decide +kernel
      have hl : raw9516step2Labels = raw9516step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9516step1 raw9516step1Labels permutation10 permutation2
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw9517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9517step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9517step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9517 raw9517Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw9517 raw9517Labels = mixedMoment B raw9517step0 raw9517step0Labels := by
      have hz : ∀ j, raw9517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9517step0 = (fun i j => raw9517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9517step0 raw9517; decide +kernel
      have hl : raw9517step0Labels = raw9517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9517 raw9517Labels permutation434 hz
    mixedMoment B raw9517step0 raw9517step0Labels = mixedMoment B raw9517step1 raw9517step1Labels := by
      have ha : raw9517step1 = (fun i j => raw9517step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9517step1 raw9517step0; decide +kernel
      have hl : raw9517step1Labels = raw9517step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9517step0 raw9517step0Labels permutation32 permutation3
    mixedMoment B raw9517step1 raw9517step1Labels = mixedMoment B raw9517step2 raw9517step2Labels := by
      have ha : raw9517step2 = raw9517step1 := by apply Matrix.ext; unfold raw9517step2 raw9517step1; decide +kernel
      have hl : raw9517step1Labels = labelEmbedding6 ∘ raw9517step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9517step1 raw9517step1Labels raw9517step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw9518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9518 raw9518Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw9518 raw9518Labels = mixedMoment B raw9518step0 raw9518step0Labels := by
      have hz : ∀ j, raw9518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9518step0 = (fun i j => raw9518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9518step0 raw9518; decide +kernel
      have hl : raw9518step0Labels = raw9518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9518 raw9518Labels permutation434 hz
    mixedMoment B raw9518step0 raw9518step0Labels = mixedMoment B raw9518step1 raw9518step1Labels := by
      have ha : raw9518step1 = (fun i j => raw9518step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9518step1 raw9518step0; decide +kernel
      have hl : raw9518step1Labels = raw9518step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9518step0 raw9518step0Labels permutation34 permutation2
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw9519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9519 raw9519Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw9519 raw9519Labels = mixedMoment B raw9519step0 raw9519step0Labels := by
      have ha : raw9519step0 = (fun i j => raw9519 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9519step0 raw9519; decide +kernel
      have hl : raw9519step0Labels = raw9519Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9519 raw9519Labels permutation202 permutation2
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw9520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9520 raw9520Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw9520 raw9520Labels = mixedMoment B raw9520step0 raw9520step0Labels := by
      have hz : ∀ j, raw9520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9520step0 = (fun i j => raw9520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9520step0 raw9520; decide +kernel
      have hl : raw9520step0Labels = raw9520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9520 raw9520Labels permutation434 hz
    mixedMoment B raw9520step0 raw9520step0Labels = mixedMoment B raw9520step1 raw9520step1Labels := by
      have ha : raw9520step1 = (fun i j => raw9520step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9520step1 raw9520step0; decide +kernel
      have hl : raw9520step1Labels = raw9520step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9520step0 raw9520step0Labels permutation34 permutation2
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw9521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9521step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9521 raw9521Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw9521 raw9521Labels = mixedMoment B raw9521step0 raw9521step0Labels := by
      have hz : ∀ j, raw9521 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9521step0 = (fun i j => raw9521 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9521step0 raw9521; decide +kernel
      have hl : raw9521step0Labels = raw9521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9521 raw9521Labels permutation346 hz
    mixedMoment B raw9521step0 raw9521step0Labels = mixedMoment B raw9521step1 raw9521step1Labels := by
      have ha : raw9521step1 = (fun i j => raw9521step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9521step1 raw9521step0; decide +kernel
      have hl : raw9521step1Labels = raw9521step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9521step0 raw9521step0Labels permutation32 permutation3
    mixedMoment B raw9521step1 raw9521step1Labels = mixedMoment B raw9521step2 raw9521step2Labels := by
      have ha : raw9521step2 = raw9521step1 := by apply Matrix.ext; unfold raw9521step2 raw9521step1; decide +kernel
      have hl : raw9521step1Labels = labelEmbedding6 ∘ raw9521step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9521step1 raw9521step1Labels raw9521step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw9522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9522 raw9522Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw9522 raw9522Labels = mixedMoment B raw9522step0 raw9522step0Labels := by
      have hz : ∀ j, raw9522 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9522step0 = (fun i j => raw9522 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9522step0 raw9522; decide +kernel
      have hl : raw9522step0Labels = raw9522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9522 raw9522Labels permutation346 hz
    mixedMoment B raw9522step0 raw9522step0Labels = mixedMoment B raw9522step1 raw9522step1Labels := by
      have ha : raw9522step1 = (fun i j => raw9522step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9522step1 raw9522step0; decide +kernel
      have hl : raw9522step1Labels = raw9522step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9522step0 raw9522step0Labels permutation34 permutation2
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw9523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9523 raw9523Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw9523 raw9523Labels = mixedMoment B raw9523step0 raw9523step0Labels := by
      have ha : raw9523step0 = (fun i j => raw9523 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9523step0 raw9523; decide +kernel
      have hl : raw9523step0Labels = raw9523Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9523 raw9523Labels permutation178 permutation2
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw9524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9524 raw9524Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw9524 raw9524Labels = mixedMoment B raw9524step0 raw9524step0Labels := by
      have hz : ∀ j, raw9524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9524step0 = (fun i j => raw9524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9524step0 raw9524; decide +kernel
      have hl : raw9524step0Labels = raw9524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9524 raw9524Labels permutation346 hz
    mixedMoment B raw9524step0 raw9524step0Labels = mixedMoment B raw9524step1 raw9524step1Labels := by
      have ha : raw9524step1 = (fun i j => raw9524step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9524step1 raw9524step0; decide +kernel
      have hl : raw9524step1Labels = raw9524step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9524step0 raw9524step0Labels permutation34 permutation2
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw9525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9525step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9525step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9525step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9525 raw9525Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw9525 raw9525Labels = mixedMoment B raw9525step0 raw9525step0Labels := by
      have hz : ∀ j, raw9525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9525step0 = (fun i j => raw9525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9525step0 raw9525; decide +kernel
      have hl : raw9525step0Labels = raw9525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9525 raw9525Labels permutation434 hz
    mixedMoment B raw9525step0 raw9525step0Labels = mixedMoment B raw9525step1 raw9525step1Labels := by
      have hz : ∀ j, raw9525step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9525step1 = (fun i j => raw9525step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9525step1 raw9525step0; decide +kernel
      have hl : raw9525step1Labels = raw9525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9525step0 raw9525step0Labels permutation80 hz
    mixedMoment B raw9525step1 raw9525step1Labels = mixedMoment B raw9525step2 raw9525step2Labels := by
      have ha : raw9525step2 = (fun i j => raw9525step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9525step2 raw9525step1; decide +kernel
      have hl : raw9525step2Labels = raw9525step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9525step1 raw9525step1Labels permutation9 permutation3
    mixedMoment B raw9525step2 raw9525step2Labels = mixedMoment B raw9525step3 raw9525step3Labels := by
      have ha : raw9525step3 = raw9525step2 := by apply Matrix.ext; unfold raw9525step3 raw9525step2; decide +kernel
      have hl : raw9525step2Labels = labelEmbedding6 ∘ raw9525step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9525step2 raw9525step2Labels raw9525step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw9526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9526step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9526 raw9526Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw9526 raw9526Labels = mixedMoment B raw9526step0 raw9526step0Labels := by
      have hz : ∀ j, raw9526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9526step0 = (fun i j => raw9526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9526step0 raw9526; decide +kernel
      have hl : raw9526step0Labels = raw9526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9526 raw9526Labels permutation434 hz
    mixedMoment B raw9526step0 raw9526step0Labels = mixedMoment B raw9526step1 raw9526step1Labels := by
      have hz : ∀ j, raw9526step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9526step1 = (fun i j => raw9526step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9526step1 raw9526step0; decide +kernel
      have hl : raw9526step1Labels = raw9526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9526step0 raw9526step0Labels permutation80 hz
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw9527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9527 raw9527Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw9527 raw9527Labels = mixedMoment B raw9527step0 raw9527step0Labels := by
      have hz : ∀ j, raw9527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9527step0 = (fun i j => raw9527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9527step0 raw9527; decide +kernel
      have hl : raw9527step0Labels = raw9527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9527 raw9527Labels permutation434 hz
    mixedMoment B raw9527step0 raw9527step0Labels = mixedMoment B raw9527step1 raw9527step1Labels := by
      have ha : raw9527step1 = (fun i j => raw9527step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9527step1 raw9527step0; decide +kernel
      have hl : raw9527step1Labels = raw9527step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9527step0 raw9527step0Labels permutation38 permutation2
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw9528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9528 raw9528Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw9528 raw9528Labels = mixedMoment B raw9528step0 raw9528step0Labels := by
      have hz : ∀ j, raw9528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9528step0 = (fun i j => raw9528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9528step0 raw9528; decide +kernel
      have hl : raw9528step0Labels = raw9528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9528 raw9528Labels permutation346 hz
    mixedMoment B raw9528step0 raw9528step0Labels = mixedMoment B raw9528step1 raw9528step1Labels := by
      have ha : raw9528step1 = (fun i j => raw9528step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9528step1 raw9528step0; decide +kernel
      have hl : raw9528step1Labels = raw9528step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9528step0 raw9528step0Labels permutation38 permutation2
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw9529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw9529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw9529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw9529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9529 raw9529Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw9529 raw9529Labels = mixedMoment B raw9529step0 raw9529step0Labels := by
      have hz : ∀ j, raw9529 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9529step0 = (fun i j => raw9529 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9529step0 raw9529; decide +kernel
      have hl : raw9529step0Labels = raw9529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9529 raw9529Labels permutation434 hz
    mixedMoment B raw9529step0 raw9529step0Labels = mixedMoment B raw9529step1 raw9529step1Labels := by
      have hz : ∀ j, raw9529step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9529step1 = (fun i j => raw9529step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9529step1 raw9529step0; decide +kernel
      have hl : raw9529step1Labels = raw9529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9529step0 raw9529step0Labels permutation80 hz
    mixedMoment B raw9529step1 raw9529step1Labels = mixedMoment B raw9529step2 raw9529step2Labels := by
      have ha : raw9529step2 = (fun i j => raw9529step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9529step2 raw9529step1; decide +kernel
      have hl : raw9529step2Labels = raw9529step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9529step1 raw9529step1Labels permutation9 permutation2
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw9530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw9530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9530 raw9530Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw9530 raw9530Labels = mixedMoment B raw9530step0 raw9530step0Labels := by
      have hz : ∀ j, raw9530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9530step0 = (fun i j => raw9530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9530step0 raw9530; decide +kernel
      have hl : raw9530step0Labels = raw9530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9530 raw9530Labels permutation434 hz
    mixedMoment B raw9530step0 raw9530step0Labels = mixedMoment B raw9530step1 raw9530step1Labels := by
      have hz : ∀ j, raw9530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9530step1 = (fun i j => raw9530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9530step1 raw9530step0; decide +kernel
      have hl : raw9530step1Labels = raw9530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9530step0 raw9530step0Labels permutation80 hz
    mixedMoment B raw9530step1 raw9530step1Labels = mixedMoment B raw9530step2 raw9530step2Labels := by
      have ha : raw9530step2 = (fun i j => raw9530step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9530step2 raw9530step1; decide +kernel
      have hl : raw9530step2Labels = raw9530step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9530step1 raw9530step1Labels permutation10 permutation2
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw9531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9531step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw9531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9531 raw9531Labels = mixedMoment B node4030 node4030Labels := by
  calc
    mixedMoment B raw9531 raw9531Labels = mixedMoment B raw9531step0 raw9531step0Labels := by
      have hz : ∀ j, raw9531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9531step0 = (fun i j => raw9531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9531step0 raw9531; decide +kernel
      have hl : raw9531step0Labels = raw9531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9531 raw9531Labels permutation434 hz
    mixedMoment B raw9531step0 raw9531step0Labels = mixedMoment B raw9531step1 raw9531step1Labels := by
      have hz : ∀ j, raw9531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9531step1 = (fun i j => raw9531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9531step1 raw9531step0; decide +kernel
      have hl : raw9531step1Labels = raw9531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9531step0 raw9531step0Labels permutation80 hz
    mixedMoment B raw9531step1 raw9531step1Labels = mixedMoment B raw9531step2 raw9531step2Labels := by
      have ha : raw9531step2 = (fun i j => raw9531step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9531step2 raw9531step1; decide +kernel
      have hl : raw9531step2Labels = raw9531step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9531step1 raw9531step1Labels permutation8 permutation3
    _ = mixedMoment B node4030 node4030Labels := by rfl

def raw9532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9532 raw9532Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw9532 raw9532Labels = mixedMoment B raw9532step0 raw9532step0Labels := by
      have hz : ∀ j, raw9532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9532step0 = (fun i j => raw9532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9532step0 raw9532; decide +kernel
      have hl : raw9532step0Labels = raw9532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9532 raw9532Labels permutation434 hz
    mixedMoment B raw9532step0 raw9532step0Labels = mixedMoment B raw9532step1 raw9532step1Labels := by
      have ha : raw9532step1 = (fun i j => raw9532step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9532step1 raw9532step0; decide +kernel
      have hl : raw9532step1Labels = raw9532step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9532step0 raw9532step0Labels permutation149 permutation3
    mixedMoment B raw9532step1 raw9532step1Labels = mixedMoment B raw9532step2 raw9532step2Labels := by
      have ha : raw9532step2 = -raw9532step1 := by apply Matrix.ext; change ∀ i j, raw9532step2 i j = -(raw9532step1 i j); unfold raw9532step2 raw9532step1; decide +kernel
      have hl : raw9532step2Labels = raw9532step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4027 node4027Labels := by rfl

def raw9533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9533step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9533 raw9533Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw9533 raw9533Labels = mixedMoment B raw9533step0 raw9533step0Labels := by
      have hz : ∀ j, raw9533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9533step0 = (fun i j => raw9533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9533step0 raw9533; decide +kernel
      have hl : raw9533step0Labels = raw9533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9533 raw9533Labels permutation346 hz
    mixedMoment B raw9533step0 raw9533step0Labels = mixedMoment B raw9533step1 raw9533step1Labels := by
      have ha : raw9533step1 = (fun i j => raw9533step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9533step1 raw9533step0; decide +kernel
      have hl : raw9533step1Labels = raw9533step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9533step0 raw9533step0Labels permutation149 permutation3
    mixedMoment B raw9533step1 raw9533step1Labels = mixedMoment B raw9533step2 raw9533step2Labels := by
      have ha : raw9533step2 = -raw9533step1 := by apply Matrix.ext; change ∀ i j, raw9533step2 i j = -(raw9533step1 i j); unfold raw9533step2 raw9533step1; decide +kernel
      have hl : raw9533step2Labels = raw9533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4027 node4027Labels := by rfl

def raw9534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9534 raw9534Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw9534 raw9534Labels = mixedMoment B raw9534step0 raw9534step0Labels := by
      have hz : ∀ j, raw9534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9534step0 = (fun i j => raw9534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9534step0 raw9534; decide +kernel
      have hl : raw9534step0Labels = raw9534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9534 raw9534Labels permutation434 hz
    mixedMoment B raw9534step0 raw9534step0Labels = mixedMoment B raw9534step1 raw9534step1Labels := by
      have hz : ∀ j, raw9534step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9534step1 = (fun i j => raw9534step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9534step1 raw9534step0; decide +kernel
      have hl : raw9534step1Labels = raw9534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9534step0 raw9534step0Labels permutation80 hz
    mixedMoment B raw9534step1 raw9534step1Labels = mixedMoment B raw9534step2 raw9534step2Labels := by
      have ha : raw9534step2 = (fun i j => raw9534step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9534step2 raw9534step1; decide +kernel
      have hl : raw9534step2Labels = raw9534step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9534step1 raw9534step1Labels permutation29 permutation6
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw9535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9535step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9535 raw9535Labels = mixedMoment B node1302 node1302Labels := by
  calc
    mixedMoment B raw9535 raw9535Labels = mixedMoment B raw9535step0 raw9535step0Labels := by
      have hz : ∀ j, raw9535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9535step0 = (fun i j => raw9535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9535step0 raw9535; decide +kernel
      have hl : raw9535step0Labels = raw9535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9535 raw9535Labels permutation434 hz
    mixedMoment B raw9535step0 raw9535step0Labels = mixedMoment B raw9535step1 raw9535step1Labels := by
      have hz : ∀ j, raw9535step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9535step1 = (fun i j => raw9535step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9535step1 raw9535step0; decide +kernel
      have hl : raw9535step1Labels = raw9535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9535step0 raw9535step0Labels permutation80 hz
    mixedMoment B raw9535step1 raw9535step1Labels = mixedMoment B raw9535step2 raw9535step2Labels := by
      have ha : raw9535step2 = (fun i j => raw9535step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9535step2 raw9535step1; decide +kernel
      have hl : raw9535step2Labels = raw9535step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9535step1 raw9535step1Labels permutation8 permutation3
    _ = mixedMoment B node1302 node1302Labels := by rfl

def raw9536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9536 raw9536Labels = mixedMoment B node2961 node2961Labels := by
  calc
    mixedMoment B raw9536 raw9536Labels = mixedMoment B raw9536step0 raw9536step0Labels := by
      have hz : ∀ j, raw9536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9536step0 = (fun i j => raw9536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9536step0 raw9536; decide +kernel
      have hl : raw9536step0Labels = raw9536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9536 raw9536Labels permutation434 hz
    mixedMoment B raw9536step0 raw9536step0Labels = mixedMoment B raw9536step1 raw9536step1Labels := by
      have ha : raw9536step1 = (fun i j => raw9536step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9536step1 raw9536step0; decide +kernel
      have hl : raw9536step1Labels = raw9536step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9536step0 raw9536step0Labels permutation38 permutation3
    _ = mixedMoment B node2961 node2961Labels := by rfl

def raw9537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9537 raw9537Labels = mixedMoment B node2961 node2961Labels := by
  calc
    mixedMoment B raw9537 raw9537Labels = mixedMoment B raw9537step0 raw9537step0Labels := by
      have hz : ∀ j, raw9537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9537step0 = (fun i j => raw9537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9537step0 raw9537; decide +kernel
      have hl : raw9537step0Labels = raw9537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9537 raw9537Labels permutation346 hz
    mixedMoment B raw9537step0 raw9537step0Labels = mixedMoment B raw9537step1 raw9537step1Labels := by
      have ha : raw9537step1 = (fun i j => raw9537step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9537step1 raw9537step0; decide +kernel
      have hl : raw9537step1Labels = raw9537step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9537step0 raw9537step0Labels permutation38 permutation3
    _ = mixedMoment B node2961 node2961Labels := by rfl

def raw9538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9538step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9538 raw9538Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw9538 raw9538Labels = mixedMoment B raw9538step0 raw9538step0Labels := by
      have hz : ∀ j, raw9538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9538step0 = (fun i j => raw9538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9538step0 raw9538; decide +kernel
      have hl : raw9538step0Labels = raw9538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9538 raw9538Labels permutation434 hz
    mixedMoment B raw9538step0 raw9538step0Labels = mixedMoment B raw9538step1 raw9538step1Labels := by
      have hz : ∀ j, raw9538step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9538step1 = (fun i j => raw9538step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9538step1 raw9538step0; decide +kernel
      have hl : raw9538step1Labels = raw9538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9538step0 raw9538step0Labels permutation80 hz
    mixedMoment B raw9538step1 raw9538step1Labels = mixedMoment B raw9538step2 raw9538step2Labels := by
      have ha : raw9538step2 = (fun i j => raw9538step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9538step2 raw9538step1; decide +kernel
      have hl : raw9538step2Labels = raw9538step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9538step1 raw9538step1Labels permutation12 permutation3
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw9539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9539 raw9539Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw9539 raw9539Labels = mixedMoment B raw9539step0 raw9539step0Labels := by
      have hz : ∀ j, raw9539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9539step0 = (fun i j => raw9539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9539step0 raw9539; decide +kernel
      have hl : raw9539step0Labels = raw9539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9539 raw9539Labels permutation434 hz
    mixedMoment B raw9539step0 raw9539step0Labels = mixedMoment B raw9539step1 raw9539step1Labels := by
      have ha : raw9539step1 = (fun i j => raw9539step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9539step1 raw9539step0; decide +kernel
      have hl : raw9539step1Labels = raw9539step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9539step0 raw9539step0Labels permutation32 permutation3
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw9540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9540 raw9540Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw9540 raw9540Labels = mixedMoment B raw9540step0 raw9540step0Labels := by
      have hz : ∀ j, raw9540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9540step0 = (fun i j => raw9540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9540step0 raw9540; decide +kernel
      have hl : raw9540step0Labels = raw9540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9540 raw9540Labels permutation434 hz
    mixedMoment B raw9540step0 raw9540step0Labels = mixedMoment B raw9540step1 raw9540step1Labels := by
      have ha : raw9540step1 = (fun i j => raw9540step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9540step1 raw9540step0; decide +kernel
      have hl : raw9540step1Labels = raw9540step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9540step0 raw9540step0Labels permutation32 permutation3
    _ = mixedMoment B node2885 node2885Labels := by rfl

def raw9541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9541 raw9541Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw9541 raw9541Labels = mixedMoment B raw9541step0 raw9541step0Labels := by
      have ha : raw9541step0 = (fun i j => raw9541 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9541step0 raw9541; decide +kernel
      have hl : raw9541step0Labels = raw9541Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9541 raw9541Labels permutation200 permutation3
    _ = mixedMoment B node2928 node2928Labels := by rfl

def raw9542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9542 raw9542Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw9542 raw9542Labels = mixedMoment B raw9542step0 raw9542step0Labels := by
      have hz : ∀ j, raw9542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9542step0 = (fun i j => raw9542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9542step0 raw9542; decide +kernel
      have hl : raw9542step0Labels = raw9542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9542 raw9542Labels permutation434 hz
    mixedMoment B raw9542step0 raw9542step0Labels = mixedMoment B raw9542step1 raw9542step1Labels := by
      have ha : raw9542step1 = (fun i j => raw9542step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9542step1 raw9542step0; decide +kernel
      have hl : raw9542step1Labels = raw9542step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9542step0 raw9542step0Labels permutation36 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw9543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9543 raw9543Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw9543 raw9543Labels = mixedMoment B raw9543step0 raw9543step0Labels := by
      have hz : ∀ j, raw9543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9543step0 = (fun i j => raw9543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9543step0 raw9543; decide +kernel
      have hl : raw9543step0Labels = raw9543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9543 raw9543Labels permutation346 hz
    mixedMoment B raw9543step0 raw9543step0Labels = mixedMoment B raw9543step1 raw9543step1Labels := by
      have ha : raw9543step1 = (fun i j => raw9543step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9543step1 raw9543step0; decide +kernel
      have hl : raw9543step1Labels = raw9543step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9543step0 raw9543step0Labels permutation32 permutation3
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw9544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9544 raw9544Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw9544 raw9544Labels = mixedMoment B raw9544step0 raw9544step0Labels := by
      have hz : ∀ j, raw9544 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9544step0 = (fun i j => raw9544 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9544step0 raw9544; decide +kernel
      have hl : raw9544step0Labels = raw9544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9544 raw9544Labels permutation346 hz
    mixedMoment B raw9544step0 raw9544step0Labels = mixedMoment B raw9544step1 raw9544step1Labels := by
      have ha : raw9544step1 = (fun i j => raw9544step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9544step1 raw9544step0; decide +kernel
      have hl : raw9544step1Labels = raw9544step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9544step0 raw9544step0Labels permutation32 permutation3
    _ = mixedMoment B node2885 node2885Labels := by rfl

def raw9545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9545 raw9545Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw9545 raw9545Labels = mixedMoment B raw9545step0 raw9545step0Labels := by
      have ha : raw9545step0 = (fun i j => raw9545 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9545step0 raw9545; decide +kernel
      have hl : raw9545step0Labels = raw9545Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9545 raw9545Labels permutation176 permutation3
    _ = mixedMoment B node2928 node2928Labels := by rfl

def raw9546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9546 raw9546Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw9546 raw9546Labels = mixedMoment B raw9546step0 raw9546step0Labels := by
      have hz : ∀ j, raw9546 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9546step0 = (fun i j => raw9546 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9546step0 raw9546; decide +kernel
      have hl : raw9546step0Labels = raw9546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9546 raw9546Labels permutation346 hz
    mixedMoment B raw9546step0 raw9546step0Labels = mixedMoment B raw9546step1 raw9546step1Labels := by
      have ha : raw9546step1 = (fun i j => raw9546step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9546step1 raw9546step0; decide +kernel
      have hl : raw9546step1Labels = raw9546step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9546step0 raw9546step0Labels permutation36 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw9547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9547step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9547 raw9547Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw9547 raw9547Labels = mixedMoment B raw9547step0 raw9547step0Labels := by
      have hz : ∀ j, raw9547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9547step0 = (fun i j => raw9547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9547step0 raw9547; decide +kernel
      have hl : raw9547step0Labels = raw9547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9547 raw9547Labels permutation434 hz
    mixedMoment B raw9547step0 raw9547step0Labels = mixedMoment B raw9547step1 raw9547step1Labels := by
      have hz : ∀ j, raw9547step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9547step1 = (fun i j => raw9547step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9547step1 raw9547step0; decide +kernel
      have hl : raw9547step1Labels = raw9547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9547step0 raw9547step0Labels permutation80 hz
    mixedMoment B raw9547step1 raw9547step1Labels = mixedMoment B raw9547step2 raw9547step2Labels := by
      have ha : raw9547step2 = (fun i j => raw9547step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9547step2 raw9547step1; decide +kernel
      have hl : raw9547step2Labels = raw9547step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9547step1 raw9547step1Labels permutation9 permutation3
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw9548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9548step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw9548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9548 raw9548Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw9548 raw9548Labels = mixedMoment B raw9548step0 raw9548step0Labels := by
      have hz : ∀ j, raw9548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9548step0 = (fun i j => raw9548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9548step0 raw9548; decide +kernel
      have hl : raw9548step0Labels = raw9548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9548 raw9548Labels permutation434 hz
    mixedMoment B raw9548step0 raw9548step0Labels = mixedMoment B raw9548step1 raw9548step1Labels := by
      have hz : ∀ j, raw9548step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9548step1 = (fun i j => raw9548step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9548step1 raw9548step0; decide +kernel
      have hl : raw9548step1Labels = raw9548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9548step0 raw9548step0Labels permutation80 hz
    mixedMoment B raw9548step1 raw9548step1Labels = mixedMoment B raw9548step2 raw9548step2Labels := by
      have ha : raw9548step2 = (fun i j => raw9548step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9548step2 raw9548step1; decide +kernel
      have hl : raw9548step2Labels = raw9548step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9548step1 raw9548step1Labels permutation9 permutation3
    _ = mixedMoment B node2888 node2888Labels := by rfl

def raw9549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9549 raw9549Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw9549 raw9549Labels = mixedMoment B raw9549step0 raw9549step0Labels := by
      have hz : ∀ j, raw9549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9549step0 = (fun i j => raw9549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9549step0 raw9549; decide +kernel
      have hl : raw9549step0Labels = raw9549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9549 raw9549Labels permutation434 hz
    mixedMoment B raw9549step0 raw9549step0Labels = mixedMoment B raw9549step1 raw9549step1Labels := by
      have ha : raw9549step1 = (fun i j => raw9549step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9549step1 raw9549step0; decide +kernel
      have hl : raw9549step1Labels = raw9549step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9549step0 raw9549step0Labels permutation39 permutation3
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw9550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9550Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9550step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9550 raw9550Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw9550 raw9550Labels = mixedMoment B raw9550step0 raw9550step0Labels := by
      have hz : ∀ j, raw9550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9550step0 = (fun i j => raw9550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9550step0 raw9550; decide +kernel
      have hl : raw9550step0Labels = raw9550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9550 raw9550Labels permutation346 hz
    mixedMoment B raw9550step0 raw9550step0Labels = mixedMoment B raw9550step1 raw9550step1Labels := by
      have ha : raw9550step1 = (fun i j => raw9550step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9550step1 raw9550step0; decide +kernel
      have hl : raw9550step1Labels = raw9550step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9550step0 raw9550step0Labels permutation39 permutation3
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw9551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw9551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw9551step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw9551step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9551 raw9551Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw9551 raw9551Labels = mixedMoment B raw9551step0 raw9551step0Labels := by
      have hz : ∀ j, raw9551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9551step0 = (fun i j => raw9551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9551step0 raw9551; decide +kernel
      have hl : raw9551step0Labels = raw9551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9551 raw9551Labels permutation434 hz
    mixedMoment B raw9551step0 raw9551step0Labels = mixedMoment B raw9551step1 raw9551step1Labels := by
      have hz : ∀ j, raw9551step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9551step1 = (fun i j => raw9551step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9551step1 raw9551step0; decide +kernel
      have hl : raw9551step1Labels = raw9551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9551step0 raw9551step0Labels permutation80 hz
    mixedMoment B raw9551step1 raw9551step1Labels = mixedMoment B raw9551step2 raw9551step2Labels := by
      have ha : raw9551step2 = (fun i j => raw9551step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9551step2 raw9551step1; decide +kernel
      have hl : raw9551step2Labels = raw9551step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9551step1 raw9551step1Labels permutation9 permutation3
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw9552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw9552step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9552 raw9552Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw9552 raw9552Labels = mixedMoment B raw9552step0 raw9552step0Labels := by
      have hz : ∀ j, raw9552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9552step0 = (fun i j => raw9552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9552step0 raw9552; decide +kernel
      have hl : raw9552step0Labels = raw9552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9552 raw9552Labels permutation434 hz
    mixedMoment B raw9552step0 raw9552step0Labels = mixedMoment B raw9552step1 raw9552step1Labels := by
      have hz : ∀ j, raw9552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9552step1 = (fun i j => raw9552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9552step1 raw9552step0; decide +kernel
      have hl : raw9552step1Labels = raw9552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9552step0 raw9552step0Labels permutation80 hz
    mixedMoment B raw9552step1 raw9552step1Labels = mixedMoment B raw9552step2 raw9552step2Labels := by
      have ha : raw9552step2 = (fun i j => raw9552step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9552step2 raw9552step1; decide +kernel
      have hl : raw9552step2Labels = raw9552step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9552step1 raw9552step1Labels permutation8 permutation3
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw9553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9553step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9553step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9553step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9553step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9553 raw9553Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw9553 raw9553Labels = mixedMoment B raw9553step0 raw9553step0Labels := by
      have hz : ∀ j, raw9553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9553step0 = (fun i j => raw9553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9553step0 raw9553; decide +kernel
      have hl : raw9553step0Labels = raw9553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9553 raw9553Labels permutation434 hz
    mixedMoment B raw9553step0 raw9553step0Labels = mixedMoment B raw9553step1 raw9553step1Labels := by
      have hz : ∀ j, raw9553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9553step1 = (fun i j => raw9553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9553step1 raw9553step0; decide +kernel
      have hl : raw9553step1Labels = raw9553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9553step0 raw9553step0Labels permutation80 hz
    mixedMoment B raw9553step1 raw9553step1Labels = mixedMoment B raw9553step2 raw9553step2Labels := by
      have ha : raw9553step2 = (fun i j => raw9553step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9553step2 raw9553step1; decide +kernel
      have hl : raw9553step2Labels = raw9553step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9553step1 raw9553step1Labels permutation29 permutation7
    mixedMoment B raw9553step2 raw9553step2Labels = mixedMoment B raw9553step3 raw9553step3Labels := by
      have ha : raw9553step3 = raw9553step2 := by apply Matrix.ext; unfold raw9553step3 raw9553step2; decide +kernel
      have hl : raw9553step2Labels = labelEmbedding1 ∘ raw9553step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9553step2 raw9553step2Labels raw9553step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw9554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9554step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9554 raw9554Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw9554 raw9554Labels = mixedMoment B raw9554step0 raw9554step0Labels := by
      have hz : ∀ j, raw9554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9554step0 = (fun i j => raw9554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9554step0 raw9554; decide +kernel
      have hl : raw9554step0Labels = raw9554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9554 raw9554Labels permutation434 hz
    mixedMoment B raw9554step0 raw9554step0Labels = mixedMoment B raw9554step1 raw9554step1Labels := by
      have ha : raw9554step1 = (fun i j => raw9554step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9554step1 raw9554step0; decide +kernel
      have hl : raw9554step1Labels = raw9554step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9554step0 raw9554step0Labels permutation137 permutation7
    mixedMoment B raw9554step1 raw9554step1Labels = mixedMoment B raw9554step2 raw9554step2Labels := by
      have ha : raw9554step2 = raw9554step1 := by apply Matrix.ext; unfold raw9554step2 raw9554step1; decide +kernel
      have hl : raw9554step1Labels = labelEmbedding1 ∘ raw9554step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9554step1 raw9554step1Labels raw9554step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw9555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9555step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9555step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9555 raw9555Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw9555 raw9555Labels = mixedMoment B raw9555step0 raw9555step0Labels := by
      have hz : ∀ j, raw9555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9555step0 = (fun i j => raw9555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9555step0 raw9555; decide +kernel
      have hl : raw9555step0Labels = raw9555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9555 raw9555Labels permutation346 hz
    mixedMoment B raw9555step0 raw9555step0Labels = mixedMoment B raw9555step1 raw9555step1Labels := by
      have ha : raw9555step1 = (fun i j => raw9555step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9555step1 raw9555step0; decide +kernel
      have hl : raw9555step1Labels = raw9555step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9555step0 raw9555step0Labels permutation137 permutation7
    mixedMoment B raw9555step1 raw9555step1Labels = mixedMoment B raw9555step2 raw9555step2Labels := by
      have ha : raw9555step2 = raw9555step1 := by apply Matrix.ext; unfold raw9555step2 raw9555step1; decide +kernel
      have hl : raw9555step1Labels = labelEmbedding1 ∘ raw9555step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9555step1 raw9555step1Labels raw9555step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw9556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9556step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9556step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9556step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9556step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9556step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9556step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9556step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9556 raw9556Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw9556 raw9556Labels = mixedMoment B raw9556step0 raw9556step0Labels := by
      have hz : ∀ j, raw9556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9556step0 = (fun i j => raw9556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9556step0 raw9556; decide +kernel
      have hl : raw9556step0Labels = raw9556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9556 raw9556Labels permutation434 hz
    mixedMoment B raw9556step0 raw9556step0Labels = mixedMoment B raw9556step1 raw9556step1Labels := by
      have hz : ∀ j, raw9556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9556step1 = (fun i j => raw9556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9556step1 raw9556step0; decide +kernel
      have hl : raw9556step1Labels = raw9556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9556step0 raw9556step0Labels permutation80 hz
    mixedMoment B raw9556step1 raw9556step1Labels = mixedMoment B raw9556step2 raw9556step2Labels := by
      have ha : raw9556step2 = (fun i j => raw9556step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9556step2 raw9556step1; decide +kernel
      have hl : raw9556step2Labels = raw9556step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9556step1 raw9556step1Labels permutation10 permutation7
    mixedMoment B raw9556step2 raw9556step2Labels = mixedMoment B raw9556step3 raw9556step3Labels := by
      have ha : raw9556step3 = -raw9556step2 := by apply Matrix.ext; change ∀ i j, raw9556step3 i j = -(raw9556step2 i j); unfold raw9556step3 raw9556step2; decide +kernel
      have hl : raw9556step3Labels = raw9556step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9556step3 raw9556step3Labels = mixedMoment B raw9556step4 raw9556step4Labels := by
      have ha : raw9556step4 = raw9556step3 := by apply Matrix.ext; unfold raw9556step4 raw9556step3; decide +kernel
      have hl : raw9556step3Labels = labelEmbedding1 ∘ raw9556step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9556step3 raw9556step3Labels raw9556step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw9557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9557Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9557step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9557step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw9557step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9557step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9557step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9557step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9557step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9557 raw9557Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw9557 raw9557Labels = mixedMoment B raw9557step0 raw9557step0Labels := by
      have hz : ∀ j, raw9557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9557step0 = (fun i j => raw9557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9557step0 raw9557; decide +kernel
      have hl : raw9557step0Labels = raw9557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9557 raw9557Labels permutation434 hz
    mixedMoment B raw9557step0 raw9557step0Labels = mixedMoment B raw9557step1 raw9557step1Labels := by
      have hz : ∀ j, raw9557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9557step1 = (fun i j => raw9557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9557step1 raw9557step0; decide +kernel
      have hl : raw9557step1Labels = raw9557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9557step0 raw9557step0Labels permutation80 hz
    mixedMoment B raw9557step1 raw9557step1Labels = mixedMoment B raw9557step2 raw9557step2Labels := by
      have ha : raw9557step2 = (fun i j => raw9557step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9557step2 raw9557step1; decide +kernel
      have hl : raw9557step2Labels = raw9557step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9557step1 raw9557step1Labels permutation10 permutation7
    mixedMoment B raw9557step2 raw9557step2Labels = mixedMoment B raw9557step3 raw9557step3Labels := by
      have ha : raw9557step3 = -raw9557step2 := by apply Matrix.ext; change ∀ i j, raw9557step3 i j = -(raw9557step2 i j); unfold raw9557step3 raw9557step2; decide +kernel
      have hl : raw9557step3Labels = raw9557step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9557step3 raw9557step3Labels = mixedMoment B raw9557step4 raw9557step4Labels := by
      have ha : raw9557step4 = raw9557step3 := by apply Matrix.ext; unfold raw9557step4 raw9557step3; decide +kernel
      have hl : raw9557step3Labels = labelEmbedding1 ∘ raw9557step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9557step3 raw9557step3Labels raw9557step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

def raw9558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9558step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw9558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9558step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9558step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9558step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9558 raw9558Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw9558 raw9558Labels = mixedMoment B raw9558step0 raw9558step0Labels := by
      have hz : ∀ j, raw9558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9558step0 = (fun i j => raw9558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9558step0 raw9558; decide +kernel
      have hl : raw9558step0Labels = raw9558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9558 raw9558Labels permutation434 hz
    mixedMoment B raw9558step0 raw9558step0Labels = mixedMoment B raw9558step1 raw9558step1Labels := by
      have ha : raw9558step1 = (fun i j => raw9558step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9558step1 raw9558step0; decide +kernel
      have hl : raw9558step1Labels = raw9558step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9558step0 raw9558step0Labels permutation46 permutation7
    mixedMoment B raw9558step1 raw9558step1Labels = mixedMoment B raw9558step2 raw9558step2Labels := by
      have ha : raw9558step2 = -raw9558step1 := by apply Matrix.ext; change ∀ i j, raw9558step2 i j = -(raw9558step1 i j); unfold raw9558step2 raw9558step1; decide +kernel
      have hl : raw9558step2Labels = raw9558step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9558step2 raw9558step2Labels = mixedMoment B raw9558step3 raw9558step3Labels := by
      have ha : raw9558step3 = raw9558step2 := by apply Matrix.ext; unfold raw9558step3 raw9558step2; decide +kernel
      have hl : raw9558step2Labels = labelEmbedding1 ∘ raw9558step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9558step2 raw9558step2Labels raw9558step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw9559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9559Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9559step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw9559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9559step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9559step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9559step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9559 raw9559Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw9559 raw9559Labels = mixedMoment B raw9559step0 raw9559step0Labels := by
      have hz : ∀ j, raw9559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9559step0 = (fun i j => raw9559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9559step0 raw9559; decide +kernel
      have hl : raw9559step0Labels = raw9559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9559 raw9559Labels permutation346 hz
    mixedMoment B raw9559step0 raw9559step0Labels = mixedMoment B raw9559step1 raw9559step1Labels := by
      have ha : raw9559step1 = (fun i j => raw9559step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9559step1 raw9559step0; decide +kernel
      have hl : raw9559step1Labels = raw9559step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9559step0 raw9559step0Labels permutation46 permutation7
    mixedMoment B raw9559step1 raw9559step1Labels = mixedMoment B raw9559step2 raw9559step2Labels := by
      have ha : raw9559step2 = -raw9559step1 := by apply Matrix.ext; change ∀ i j, raw9559step2 i j = -(raw9559step1 i j); unfold raw9559step2 raw9559step1; decide +kernel
      have hl : raw9559step2Labels = raw9559step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9559step2 raw9559step2Labels = mixedMoment B raw9559step3 raw9559step3Labels := by
      have ha : raw9559step3 = raw9559step2 := by apply Matrix.ext; unfold raw9559step3 raw9559step2; decide +kernel
      have hl : raw9559step2Labels = labelEmbedding1 ∘ raw9559step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9559step2 raw9559step2Labels raw9559step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw9560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9560step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9560step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9560step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9560step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9560step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9560step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9560step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9560 raw9560Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw9560 raw9560Labels = mixedMoment B raw9560step0 raw9560step0Labels := by
      have hz : ∀ j, raw9560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9560step0 = (fun i j => raw9560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9560step0 raw9560; decide +kernel
      have hl : raw9560step0Labels = raw9560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9560 raw9560Labels permutation434 hz
    mixedMoment B raw9560step0 raw9560step0Labels = mixedMoment B raw9560step1 raw9560step1Labels := by
      have hz : ∀ j, raw9560step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9560step1 = (fun i j => raw9560step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9560step1 raw9560step0; decide +kernel
      have hl : raw9560step1Labels = raw9560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9560step0 raw9560step0Labels permutation80 hz
    mixedMoment B raw9560step1 raw9560step1Labels = mixedMoment B raw9560step2 raw9560step2Labels := by
      have ha : raw9560step2 = (fun i j => raw9560step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9560step2 raw9560step1; decide +kernel
      have hl : raw9560step2Labels = raw9560step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9560step1 raw9560step1Labels permutation10 permutation7
    mixedMoment B raw9560step2 raw9560step2Labels = mixedMoment B raw9560step3 raw9560step3Labels := by
      have ha : raw9560step3 = -raw9560step2 := by apply Matrix.ext; change ∀ i j, raw9560step3 i j = -(raw9560step2 i j); unfold raw9560step3 raw9560step2; decide +kernel
      have hl : raw9560step3Labels = raw9560step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9560step3 raw9560step3Labels = mixedMoment B raw9560step4 raw9560step4Labels := by
      have ha : raw9560step4 = raw9560step3 := by apply Matrix.ext; unfold raw9560step4 raw9560step3; decide +kernel
      have hl : raw9560step3Labels = labelEmbedding1 ∘ raw9560step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9560step3 raw9560step3Labels raw9560step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw9561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9561Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9561step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw9561step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9561step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9561step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9561step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9561 raw9561Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw9561 raw9561Labels = mixedMoment B raw9561step0 raw9561step0Labels := by
      have hz : ∀ j, raw9561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9561step0 = (fun i j => raw9561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9561step0 raw9561; decide +kernel
      have hl : raw9561step0Labels = raw9561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9561 raw9561Labels permutation434 hz
    mixedMoment B raw9561step0 raw9561step0Labels = mixedMoment B raw9561step1 raw9561step1Labels := by
      have ha : raw9561step1 = (fun i j => raw9561step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9561step1 raw9561step0; decide +kernel
      have hl : raw9561step1Labels = raw9561step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9561step0 raw9561step0Labels permutation36 permutation5
    mixedMoment B raw9561step1 raw9561step1Labels = mixedMoment B raw9561step2 raw9561step2Labels := by
      have ha : raw9561step2 = -raw9561step1 := by apply Matrix.ext; change ∀ i j, raw9561step2 i j = -(raw9561step1 i j); unfold raw9561step2 raw9561step1; decide +kernel
      have hl : raw9561step2Labels = raw9561step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9561step2 raw9561step2Labels = mixedMoment B raw9561step3 raw9561step3Labels := by
      have ha : raw9561step3 = raw9561step2 := by apply Matrix.ext; unfold raw9561step3 raw9561step2; decide +kernel
      have hl : raw9561step2Labels = labelEmbedding1 ∘ raw9561step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9561step2 raw9561step2Labels raw9561step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw9562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9562step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw9562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9562step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9562step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9562step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9562 raw9562Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw9562 raw9562Labels = mixedMoment B raw9562step0 raw9562step0Labels := by
      have hz : ∀ j, raw9562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9562step0 = (fun i j => raw9562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9562step0 raw9562; decide +kernel
      have hl : raw9562step0Labels = raw9562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9562 raw9562Labels permutation434 hz
    mixedMoment B raw9562step0 raw9562step0Labels = mixedMoment B raw9562step1 raw9562step1Labels := by
      have ha : raw9562step1 = (fun i j => raw9562step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9562step1 raw9562step0; decide +kernel
      have hl : raw9562step1Labels = raw9562step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9562step0 raw9562step0Labels permutation46 permutation7
    mixedMoment B raw9562step1 raw9562step1Labels = mixedMoment B raw9562step2 raw9562step2Labels := by
      have ha : raw9562step2 = -raw9562step1 := by apply Matrix.ext; change ∀ i j, raw9562step2 i j = -(raw9562step1 i j); unfold raw9562step2 raw9562step1; decide +kernel
      have hl : raw9562step2Labels = raw9562step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9562step2 raw9562step2Labels = mixedMoment B raw9562step3 raw9562step3Labels := by
      have ha : raw9562step3 = raw9562step2 := by apply Matrix.ext; unfold raw9562step3 raw9562step2; decide +kernel
      have hl : raw9562step2Labels = labelEmbedding1 ∘ raw9562step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9562step2 raw9562step2Labels raw9562step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw9563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9563Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9563step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9563step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9563step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9563 raw9563Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw9563 raw9563Labels = mixedMoment B raw9563step0 raw9563step0Labels := by
      have ha : raw9563step0 = (fun i j => raw9563 (permutation236 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9563step0 raw9563; decide +kernel
      have hl : raw9563step0Labels = raw9563Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9563 raw9563Labels permutation236 permutation7
    mixedMoment B raw9563step0 raw9563step0Labels = mixedMoment B raw9563step1 raw9563step1Labels := by
      have ha : raw9563step1 = -raw9563step0 := by apply Matrix.ext; change ∀ i j, raw9563step1 i j = -(raw9563step0 i j); unfold raw9563step1 raw9563step0; decide +kernel
      have hl : raw9563step1Labels = raw9563step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9563step1 raw9563step1Labels = mixedMoment B raw9563step2 raw9563step2Labels := by
      have ha : raw9563step2 = raw9563step1 := by apply Matrix.ext; unfold raw9563step2 raw9563step1; decide +kernel
      have hl : raw9563step1Labels = labelEmbedding1 ∘ raw9563step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9563step1 raw9563step1Labels raw9563step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw9564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9564Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9564step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9564step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9564step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9564step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9564 raw9564Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw9564 raw9564Labels = mixedMoment B raw9564step0 raw9564step0Labels := by
      have hz : ∀ j, raw9564 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9564step0 = (fun i j => raw9564 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9564step0 raw9564; decide +kernel
      have hl : raw9564step0Labels = raw9564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9564 raw9564Labels permutation434 hz
    mixedMoment B raw9564step0 raw9564step0Labels = mixedMoment B raw9564step1 raw9564step1Labels := by
      have ha : raw9564step1 = (fun i j => raw9564step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9564step1 raw9564step0; decide +kernel
      have hl : raw9564step1Labels = raw9564step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9564step0 raw9564step0Labels permutation46 permutation7
    mixedMoment B raw9564step1 raw9564step1Labels = mixedMoment B raw9564step2 raw9564step2Labels := by
      have ha : raw9564step2 = -raw9564step1 := by apply Matrix.ext; change ∀ i j, raw9564step2 i j = -(raw9564step1 i j); unfold raw9564step2 raw9564step1; decide +kernel
      have hl : raw9564step2Labels = raw9564step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9564step2 raw9564step2Labels = mixedMoment B raw9564step3 raw9564step3Labels := by
      have ha : raw9564step3 = raw9564step2 := by apply Matrix.ext; unfold raw9564step3 raw9564step2; decide +kernel
      have hl : raw9564step2Labels = labelEmbedding1 ∘ raw9564step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9564step2 raw9564step2Labels raw9564step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw9565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9565Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9565step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw9565step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9565step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9565step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9565step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9565 raw9565Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw9565 raw9565Labels = mixedMoment B raw9565step0 raw9565step0Labels := by
      have hz : ∀ j, raw9565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9565step0 = (fun i j => raw9565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9565step0 raw9565; decide +kernel
      have hl : raw9565step0Labels = raw9565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9565 raw9565Labels permutation346 hz
    mixedMoment B raw9565step0 raw9565step0Labels = mixedMoment B raw9565step1 raw9565step1Labels := by
      have ha : raw9565step1 = (fun i j => raw9565step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9565step1 raw9565step0; decide +kernel
      have hl : raw9565step1Labels = raw9565step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9565step0 raw9565step0Labels permutation36 permutation5
    mixedMoment B raw9565step1 raw9565step1Labels = mixedMoment B raw9565step2 raw9565step2Labels := by
      have ha : raw9565step2 = -raw9565step1 := by apply Matrix.ext; change ∀ i j, raw9565step2 i j = -(raw9565step1 i j); unfold raw9565step2 raw9565step1; decide +kernel
      have hl : raw9565step2Labels = raw9565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9565step2 raw9565step2Labels = mixedMoment B raw9565step3 raw9565step3Labels := by
      have ha : raw9565step3 = raw9565step2 := by apply Matrix.ext; unfold raw9565step3 raw9565step2; decide +kernel
      have hl : raw9565step2Labels = labelEmbedding1 ∘ raw9565step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9565step2 raw9565step2Labels raw9565step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw9566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9566Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9566step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw9566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9566step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9566step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9566 raw9566Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw9566 raw9566Labels = mixedMoment B raw9566step0 raw9566step0Labels := by
      have hz : ∀ j, raw9566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9566step0 = (fun i j => raw9566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9566step0 raw9566; decide +kernel
      have hl : raw9566step0Labels = raw9566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9566 raw9566Labels permutation346 hz
    mixedMoment B raw9566step0 raw9566step0Labels = mixedMoment B raw9566step1 raw9566step1Labels := by
      have ha : raw9566step1 = (fun i j => raw9566step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9566step1 raw9566step0; decide +kernel
      have hl : raw9566step1Labels = raw9566step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9566step0 raw9566step0Labels permutation46 permutation7
    mixedMoment B raw9566step1 raw9566step1Labels = mixedMoment B raw9566step2 raw9566step2Labels := by
      have ha : raw9566step2 = -raw9566step1 := by apply Matrix.ext; change ∀ i j, raw9566step2 i j = -(raw9566step1 i j); unfold raw9566step2 raw9566step1; decide +kernel
      have hl : raw9566step2Labels = raw9566step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9566step2 raw9566step2Labels = mixedMoment B raw9566step3 raw9566step3Labels := by
      have ha : raw9566step3 = raw9566step2 := by apply Matrix.ext; unfold raw9566step3 raw9566step2; decide +kernel
      have hl : raw9566step2Labels = labelEmbedding1 ∘ raw9566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9566step2 raw9566step2Labels raw9566step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw9567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9567Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9567step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9567step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9567step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9567 raw9567Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw9567 raw9567Labels = mixedMoment B raw9567step0 raw9567step0Labels := by
      have ha : raw9567step0 = (fun i j => raw9567 (permutation232 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9567step0 raw9567; decide +kernel
      have hl : raw9567step0Labels = raw9567Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9567 raw9567Labels permutation232 permutation7
    mixedMoment B raw9567step0 raw9567step0Labels = mixedMoment B raw9567step1 raw9567step1Labels := by
      have ha : raw9567step1 = -raw9567step0 := by apply Matrix.ext; change ∀ i j, raw9567step1 i j = -(raw9567step0 i j); unfold raw9567step1 raw9567step0; decide +kernel
      have hl : raw9567step1Labels = raw9567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9567step1 raw9567step1Labels = mixedMoment B raw9567step2 raw9567step2Labels := by
      have ha : raw9567step2 = raw9567step1 := by apply Matrix.ext; unfold raw9567step2 raw9567step1; decide +kernel
      have hl : raw9567step1Labels = labelEmbedding1 ∘ raw9567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9567step1 raw9567step1Labels raw9567step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw9568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9568Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9568step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9568step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9568step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9568step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9568 raw9568Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw9568 raw9568Labels = mixedMoment B raw9568step0 raw9568step0Labels := by
      have hz : ∀ j, raw9568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9568step0 = (fun i j => raw9568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9568step0 raw9568; decide +kernel
      have hl : raw9568step0Labels = raw9568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9568 raw9568Labels permutation346 hz
    mixedMoment B raw9568step0 raw9568step0Labels = mixedMoment B raw9568step1 raw9568step1Labels := by
      have ha : raw9568step1 = (fun i j => raw9568step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9568step1 raw9568step0; decide +kernel
      have hl : raw9568step1Labels = raw9568step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9568step0 raw9568step0Labels permutation46 permutation7
    mixedMoment B raw9568step1 raw9568step1Labels = mixedMoment B raw9568step2 raw9568step2Labels := by
      have ha : raw9568step2 = -raw9568step1 := by apply Matrix.ext; change ∀ i j, raw9568step2 i j = -(raw9568step1 i j); unfold raw9568step2 raw9568step1; decide +kernel
      have hl : raw9568step2Labels = raw9568step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9568step2 raw9568step2Labels = mixedMoment B raw9568step3 raw9568step3Labels := by
      have ha : raw9568step3 = raw9568step2 := by apply Matrix.ext; unfold raw9568step3 raw9568step2; decide +kernel
      have hl : raw9568step2Labels = labelEmbedding1 ∘ raw9568step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9568step2 raw9568step2Labels raw9568step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw9569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9569Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9569step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9569step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw9569step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw9569step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9569 raw9569Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw9569 raw9569Labels = mixedMoment B raw9569step0 raw9569step0Labels := by
      have hz : ∀ j, raw9569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9569step0 = (fun i j => raw9569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9569step0 raw9569; decide +kernel
      have hl : raw9569step0Labels = raw9569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9569 raw9569Labels permutation434 hz
    mixedMoment B raw9569step0 raw9569step0Labels = mixedMoment B raw9569step1 raw9569step1Labels := by
      have hz : ∀ j, raw9569step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9569step1 = (fun i j => raw9569step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9569step1 raw9569step0; decide +kernel
      have hl : raw9569step1Labels = raw9569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9569step0 raw9569step0Labels permutation80 hz
    mixedMoment B raw9569step1 raw9569step1Labels = mixedMoment B raw9569step2 raw9569step2Labels := by
      have ha : raw9569step2 = (fun i j => raw9569step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9569step2 raw9569step1; decide +kernel
      have hl : raw9569step2Labels = raw9569step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9569step1 raw9569step1Labels permutation25 permutation5
    mixedMoment B raw9569step2 raw9569step2Labels = mixedMoment B raw9569step3 raw9569step3Labels := by
      have ha : raw9569step3 = raw9569step2 := by apply Matrix.ext; unfold raw9569step3 raw9569step2; decide +kernel
      have hl : raw9569step2Labels = labelEmbedding1 ∘ raw9569step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9569step2 raw9569step2Labels raw9569step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

def raw9570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9570Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9570step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9570step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9570step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw9570step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9570step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw9570step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9570 raw9570Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw9570 raw9570Labels = mixedMoment B raw9570step0 raw9570step0Labels := by
      have hz : ∀ j, raw9570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9570step0 = (fun i j => raw9570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9570step0 raw9570; decide +kernel
      have hl : raw9570step0Labels = raw9570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9570 raw9570Labels permutation434 hz
    mixedMoment B raw9570step0 raw9570step0Labels = mixedMoment B raw9570step1 raw9570step1Labels := by
      have hz : ∀ j, raw9570step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9570step1 = (fun i j => raw9570step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9570step1 raw9570step0; decide +kernel
      have hl : raw9570step1Labels = raw9570step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9570step0 raw9570step0Labels permutation80 hz
    mixedMoment B raw9570step1 raw9570step1Labels = mixedMoment B raw9570step2 raw9570step2Labels := by
      have ha : raw9570step2 = (fun i j => raw9570step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9570step2 raw9570step1; decide +kernel
      have hl : raw9570step2Labels = raw9570step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9570step1 raw9570step1Labels permutation24 permutation5
    mixedMoment B raw9570step2 raw9570step2Labels = mixedMoment B raw9570step3 raw9570step3Labels := by
      have ha : raw9570step3 = raw9570step2 := by apply Matrix.ext; unfold raw9570step3 raw9570step2; decide +kernel
      have hl : raw9570step2Labels = labelEmbedding1 ∘ raw9570step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9570step2 raw9570step2Labels raw9570step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw9571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9571Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9571step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9571step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9571 raw9571Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw9571 raw9571Labels = mixedMoment B raw9571step0 raw9571step0Labels := by
      have hz : ∀ j, raw9571 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9571step0 = (fun i j => raw9571 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9571step0 raw9571; decide +kernel
      have hl : raw9571step0Labels = raw9571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9571 raw9571Labels permutation434 hz
    mixedMoment B raw9571step0 raw9571step0Labels = mixedMoment B raw9571step1 raw9571step1Labels := by
      have ha : raw9571step1 = (fun i j => raw9571step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9571step1 raw9571step0; decide +kernel
      have hl : raw9571step1Labels = raw9571step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9571step0 raw9571step0Labels permutation125 permutation5
    mixedMoment B raw9571step1 raw9571step1Labels = mixedMoment B raw9571step2 raw9571step2Labels := by
      have ha : raw9571step2 = raw9571step1 := by apply Matrix.ext; unfold raw9571step2 raw9571step1; decide +kernel
      have hl : raw9571step1Labels = labelEmbedding1 ∘ raw9571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9571step1 raw9571step1Labels raw9571step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw9572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9572Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9572step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9572step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9572 raw9572Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw9572 raw9572Labels = mixedMoment B raw9572step0 raw9572step0Labels := by
      have hz : ∀ j, raw9572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9572step0 = (fun i j => raw9572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9572step0 raw9572; decide +kernel
      have hl : raw9572step0Labels = raw9572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9572 raw9572Labels permutation346 hz
    mixedMoment B raw9572step0 raw9572step0Labels = mixedMoment B raw9572step1 raw9572step1Labels := by
      have ha : raw9572step1 = (fun i j => raw9572step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9572step1 raw9572step0; decide +kernel
      have hl : raw9572step1Labels = raw9572step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9572step0 raw9572step0Labels permutation125 permutation5
    mixedMoment B raw9572step1 raw9572step1Labels = mixedMoment B raw9572step2 raw9572step2Labels := by
      have ha : raw9572step2 = raw9572step1 := by apply Matrix.ext; unfold raw9572step2 raw9572step1; decide +kernel
      have hl : raw9572step1Labels = labelEmbedding1 ∘ raw9572step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9572step1 raw9572step1Labels raw9572step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw9573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw9573Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw9573step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw9573step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9573step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9573step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9573 raw9573Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw9573 raw9573Labels = mixedMoment B raw9573step0 raw9573step0Labels := by
      have hz : ∀ j, raw9573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9573step0 = (fun i j => raw9573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9573step0 raw9573; decide +kernel
      have hl : raw9573step0Labels = raw9573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9573 raw9573Labels permutation434 hz
    mixedMoment B raw9573step0 raw9573step0Labels = mixedMoment B raw9573step1 raw9573step1Labels := by
      have hz : ∀ j, raw9573step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9573step1 = (fun i j => raw9573step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9573step1 raw9573step0; decide +kernel
      have hl : raw9573step1Labels = raw9573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9573step0 raw9573step0Labels permutation80 hz
    mixedMoment B raw9573step1 raw9573step1Labels = mixedMoment B raw9573step2 raw9573step2Labels := by
      have ha : raw9573step2 = (fun i j => raw9573step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9573step2 raw9573step1; decide +kernel
      have hl : raw9573step2Labels = raw9573step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9573step1 raw9573step1Labels permutation25 permutation5
    mixedMoment B raw9573step2 raw9573step2Labels = mixedMoment B raw9573step3 raw9573step3Labels := by
      have ha : raw9573step3 = raw9573step2 := by apply Matrix.ext; unfold raw9573step3 raw9573step2; decide +kernel
      have hl : raw9573step2Labels = labelEmbedding1 ∘ raw9573step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9573step2 raw9573step2Labels raw9573step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw9574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9574Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9574step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw9574step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9574step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9574step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9574step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9574 raw9574Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw9574 raw9574Labels = mixedMoment B raw9574step0 raw9574step0Labels := by
      have hz : ∀ j, raw9574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9574step0 = (fun i j => raw9574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9574step0 raw9574; decide +kernel
      have hl : raw9574step0Labels = raw9574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9574 raw9574Labels permutation434 hz
    mixedMoment B raw9574step0 raw9574step0Labels = mixedMoment B raw9574step1 raw9574step1Labels := by
      have hz : ∀ j, raw9574step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9574step1 = (fun i j => raw9574step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9574step1 raw9574step0; decide +kernel
      have hl : raw9574step1Labels = raw9574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9574step0 raw9574step0Labels permutation80 hz
    mixedMoment B raw9574step1 raw9574step1Labels = mixedMoment B raw9574step2 raw9574step2Labels := by
      have ha : raw9574step2 = (fun i j => raw9574step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9574step2 raw9574step1; decide +kernel
      have hl : raw9574step2Labels = raw9574step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9574step1 raw9574step1Labels permutation29 permutation7
    mixedMoment B raw9574step2 raw9574step2Labels = mixedMoment B raw9574step3 raw9574step3Labels := by
      have ha : raw9574step3 = raw9574step2 := by apply Matrix.ext; unfold raw9574step3 raw9574step2; decide +kernel
      have hl : raw9574step2Labels = labelEmbedding1 ∘ raw9574step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9574step2 raw9574step2Labels raw9574step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3545 node3545Labels := by rfl

def raw9575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9575 raw9575Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw9575 raw9575Labels = mixedMoment B raw9575step0 raw9575step0Labels := by
      have hz : ∀ j, raw9575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9575step0 = (fun i j => raw9575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9575step0 raw9575; decide +kernel
      have hl : raw9575step0Labels = raw9575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9575 raw9575Labels permutation434 hz
    mixedMoment B raw9575step0 raw9575step0Labels = mixedMoment B raw9575step1 raw9575step1Labels := by
      have hz : ∀ j, raw9575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9575step1 = (fun i j => raw9575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9575step1 raw9575step0; decide +kernel
      have hl : raw9575step1Labels = raw9575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9575step0 raw9575step0Labels permutation80 hz
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw9576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9576 raw9576Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw9576 raw9576Labels = mixedMoment B raw9576step0 raw9576step0Labels := by
      have hz : ∀ j, raw9576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9576step0 = (fun i j => raw9576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9576step0 raw9576; decide +kernel
      have hl : raw9576step0Labels = raw9576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9576 raw9576Labels permutation434 hz
    mixedMoment B raw9576step0 raw9576step0Labels = mixedMoment B raw9576step1 raw9576step1Labels := by
      have hz : ∀ j, raw9576step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9576step1 = (fun i j => raw9576step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9576step1 raw9576step0; decide +kernel
      have hl : raw9576step1Labels = raw9576step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9576step0 raw9576step0Labels permutation80 hz
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw9577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9577 raw9577Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw9577 raw9577Labels = mixedMoment B raw9577step0 raw9577step0Labels := by
      have hz : ∀ j, raw9577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9577step0 = (fun i j => raw9577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9577step0 raw9577; decide +kernel
      have hl : raw9577step0Labels = raw9577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9577 raw9577Labels permutation434 hz
    mixedMoment B raw9577step0 raw9577step0Labels = mixedMoment B raw9577step1 raw9577step1Labels := by
      have ha : raw9577step1 = (fun i j => raw9577step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9577step1 raw9577step0; decide +kernel
      have hl : raw9577step1Labels = raw9577step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9577step0 raw9577step0Labels permutation38 permutation2
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw9578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9578 raw9578Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw9578 raw9578Labels = mixedMoment B raw9578step0 raw9578step0Labels := by
      have hz : ∀ j, raw9578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9578step0 = (fun i j => raw9578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9578step0 raw9578; decide +kernel
      have hl : raw9578step0Labels = raw9578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9578 raw9578Labels permutation346 hz
    mixedMoment B raw9578step0 raw9578step0Labels = mixedMoment B raw9578step1 raw9578step1Labels := by
      have ha : raw9578step1 = (fun i j => raw9578step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9578step1 raw9578step0; decide +kernel
      have hl : raw9578step1Labels = raw9578step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9578step0 raw9578step0Labels permutation38 permutation2
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw9579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9579 raw9579Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw9579 raw9579Labels = mixedMoment B raw9579step0 raw9579step0Labels := by
      have hz : ∀ j, raw9579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9579step0 = (fun i j => raw9579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9579step0 raw9579; decide +kernel
      have hl : raw9579step0Labels = raw9579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9579 raw9579Labels permutation434 hz
    mixedMoment B raw9579step0 raw9579step0Labels = mixedMoment B raw9579step1 raw9579step1Labels := by
      have hz : ∀ j, raw9579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9579step1 = (fun i j => raw9579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9579step1 raw9579step0; decide +kernel
      have hl : raw9579step1Labels = raw9579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9579step0 raw9579step0Labels permutation80 hz
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw9580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9580Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9580 raw9580Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw9580 raw9580Labels = mixedMoment B raw9580step0 raw9580step0Labels := by
      have hz : ∀ j, raw9580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9580step0 = (fun i j => raw9580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9580step0 raw9580; decide +kernel
      have hl : raw9580step0Labels = raw9580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9580 raw9580Labels permutation434 hz
    mixedMoment B raw9580step0 raw9580step0Labels = mixedMoment B raw9580step1 raw9580step1Labels := by
      have hz : ∀ j, raw9580step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9580step1 = (fun i j => raw9580step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9580step1 raw9580step0; decide +kernel
      have hl : raw9580step1Labels = raw9580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9580step0 raw9580step0Labels permutation80 hz
    mixedMoment B raw9580step1 raw9580step1Labels = mixedMoment B raw9580step2 raw9580step2Labels := by
      have ha : raw9580step2 = (fun i j => raw9580step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9580step2 raw9580step1; decide +kernel
      have hl : raw9580step2Labels = raw9580step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9580step1 raw9580step1Labels permutation10 permutation2
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw9581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9581 raw9581Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw9581 raw9581Labels = mixedMoment B raw9581step0 raw9581step0Labels := by
      have hz : ∀ j, raw9581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9581step0 = (fun i j => raw9581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9581step0 raw9581; decide +kernel
      have hl : raw9581step0Labels = raw9581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9581 raw9581Labels permutation434 hz
    mixedMoment B raw9581step0 raw9581step0Labels = mixedMoment B raw9581step1 raw9581step1Labels := by
      have ha : raw9581step1 = (fun i j => raw9581step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9581step1 raw9581step0; decide +kernel
      have hl : raw9581step1Labels = raw9581step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9581step0 raw9581step0Labels permutation34 permutation2
    _ = mixedMoment B node1261 node1261Labels := by rfl

def raw9582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9582 raw9582Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw9582 raw9582Labels = mixedMoment B raw9582step0 raw9582step0Labels := by
      have hz : ∀ j, raw9582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9582step0 = (fun i j => raw9582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9582step0 raw9582; decide +kernel
      have hl : raw9582step0Labels = raw9582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9582 raw9582Labels permutation346 hz
    mixedMoment B raw9582step0 raw9582step0Labels = mixedMoment B raw9582step1 raw9582step1Labels := by
      have ha : raw9582step1 = (fun i j => raw9582step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9582step1 raw9582step0; decide +kernel
      have hl : raw9582step1Labels = raw9582step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9582step0 raw9582step0Labels permutation34 permutation2
    _ = mixedMoment B node1261 node1261Labels := by rfl

def raw9583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9583Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9583 raw9583Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw9583 raw9583Labels = mixedMoment B raw9583step0 raw9583step0Labels := by
      have hz : ∀ j, raw9583 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9583step0 = (fun i j => raw9583 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9583step0 raw9583; decide +kernel
      have hl : raw9583step0Labels = raw9583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9583 raw9583Labels permutation434 hz
    mixedMoment B raw9583step0 raw9583step0Labels = mixedMoment B raw9583step1 raw9583step1Labels := by
      have hz : ∀ j, raw9583step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9583step1 = (fun i j => raw9583step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9583step1 raw9583step0; decide +kernel
      have hl : raw9583step1Labels = raw9583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9583step0 raw9583step0Labels permutation80 hz
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw9584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9584 raw9584Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw9584 raw9584Labels = mixedMoment B raw9584step0 raw9584step0Labels := by
      have hz : ∀ j, raw9584 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9584step0 = (fun i j => raw9584 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9584step0 raw9584; decide +kernel
      have hl : raw9584step0Labels = raw9584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9584 raw9584Labels permutation434 hz
    mixedMoment B raw9584step0 raw9584step0Labels = mixedMoment B raw9584step1 raw9584step1Labels := by
      have ha : raw9584step1 = (fun i j => raw9584step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9584step1 raw9584step0; decide +kernel
      have hl : raw9584step1Labels = raw9584step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9584step0 raw9584step0Labels permutation40 permutation2
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw9585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9585 raw9585Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw9585 raw9585Labels = mixedMoment B raw9585step0 raw9585step0Labels := by
      have hz : ∀ j, raw9585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9585step0 = (fun i j => raw9585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9585step0 raw9585; decide +kernel
      have hl : raw9585step0Labels = raw9585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9585 raw9585Labels permutation346 hz
    mixedMoment B raw9585step0 raw9585step0Labels = mixedMoment B raw9585step1 raw9585step1Labels := by
      have ha : raw9585step1 = (fun i j => raw9585step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9585step1 raw9585step0; decide +kernel
      have hl : raw9585step1Labels = raw9585step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9585step0 raw9585step0Labels permutation40 permutation2
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw9586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9586Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9586step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9586 raw9586Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw9586 raw9586Labels = mixedMoment B raw9586step0 raw9586step0Labels := by
      have hz : ∀ j, raw9586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9586step0 = (fun i j => raw9586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9586step0 raw9586; decide +kernel
      have hl : raw9586step0Labels = raw9586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9586 raw9586Labels permutation434 hz
    mixedMoment B raw9586step0 raw9586step0Labels = mixedMoment B raw9586step1 raw9586step1Labels := by
      have hz : ∀ j, raw9586step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9586step1 = (fun i j => raw9586step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9586step1 raw9586step0; decide +kernel
      have hl : raw9586step1Labels = raw9586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9586step0 raw9586step0Labels permutation80 hz
    mixedMoment B raw9586step1 raw9586step1Labels = mixedMoment B raw9586step2 raw9586step2Labels := by
      have ha : raw9586step2 = (fun i j => raw9586step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9586step2 raw9586step1; decide +kernel
      have hl : raw9586step2Labels = raw9586step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9586step1 raw9586step1Labels permutation10 permutation2
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw9587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9587 raw9587Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw9587 raw9587Labels = mixedMoment B raw9587step0 raw9587step0Labels := by
      have hz : ∀ j, raw9587 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9587step0 = (fun i j => raw9587 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9587step0 raw9587; decide +kernel
      have hl : raw9587step0Labels = raw9587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9587 raw9587Labels permutation434 hz
    mixedMoment B raw9587step0 raw9587step0Labels = mixedMoment B raw9587step1 raw9587step1Labels := by
      have ha : raw9587step1 = (fun i j => raw9587step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9587step1 raw9587step0; decide +kernel
      have hl : raw9587step1Labels = raw9587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9587step0 raw9587step0Labels permutation34 permutation2
    _ = mixedMoment B node2632 node2632Labels := by rfl

def raw9588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9588 raw9588Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw9588 raw9588Labels = mixedMoment B raw9588step0 raw9588step0Labels := by
      have hz : ∀ j, raw9588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9588step0 = (fun i j => raw9588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9588step0 raw9588; decide +kernel
      have hl : raw9588step0Labels = raw9588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9588 raw9588Labels permutation346 hz
    mixedMoment B raw9588step0 raw9588step0Labels = mixedMoment B raw9588step1 raw9588step1Labels := by
      have ha : raw9588step1 = (fun i j => raw9588step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9588step1 raw9588step0; decide +kernel
      have hl : raw9588step1Labels = raw9588step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9588step0 raw9588step0Labels permutation34 permutation2
    _ = mixedMoment B node2632 node2632Labels := by rfl

def raw9589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9589 raw9589Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw9589 raw9589Labels = mixedMoment B raw9589step0 raw9589step0Labels := by
      have hz : ∀ j, raw9589 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9589step0 = (fun i j => raw9589 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9589step0 raw9589; decide +kernel
      have hl : raw9589step0Labels = raw9589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9589 raw9589Labels permutation434 hz
    mixedMoment B raw9589step0 raw9589step0Labels = mixedMoment B raw9589step1 raw9589step1Labels := by
      have hz : ∀ j, raw9589step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9589step1 = (fun i j => raw9589step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9589step1 raw9589step0; decide +kernel
      have hl : raw9589step1Labels = raw9589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9589step0 raw9589step0Labels permutation80 hz
    _ = mixedMoment B node2643 node2643Labels := by rfl

def raw9590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9590 raw9590Labels = mixedMoment B node2566 node2566Labels := by
  calc
    mixedMoment B raw9590 raw9590Labels = mixedMoment B raw9590step0 raw9590step0Labels := by
      have ha : raw9590step0 = (fun i j => raw9590 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9590step0 raw9590; decide +kernel
      have hl : raw9590step0Labels = raw9590Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9590 raw9590Labels permutation202 permutation2
    _ = mixedMoment B node2566 node2566Labels := by rfl

def raw9591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9591 raw9591Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw9591 raw9591Labels = mixedMoment B raw9591step0 raw9591step0Labels := by
      have hz : ∀ j, raw9591 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9591step0 = (fun i j => raw9591 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9591step0 raw9591; decide +kernel
      have hl : raw9591step0Labels = raw9591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9591 raw9591Labels permutation434 hz
    mixedMoment B raw9591step0 raw9591step0Labels = mixedMoment B raw9591step1 raw9591step1Labels := by
      have ha : raw9591step1 = (fun i j => raw9591step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9591step1 raw9591step0; decide +kernel
      have hl : raw9591step1Labels = raw9591step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9591step0 raw9591step0Labels permutation34 permutation2
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw9592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9592step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9592step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9592step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9592step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9592step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9592 raw9592Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw9592 raw9592Labels = mixedMoment B raw9592step0 raw9592step0Labels := by
      have hz : ∀ j, raw9592 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9592step0 = (fun i j => raw9592 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9592step0 raw9592; decide +kernel
      have hl : raw9592step0Labels = raw9592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9592 raw9592Labels permutation434 hz
    mixedMoment B raw9592step0 raw9592step0Labels = mixedMoment B raw9592step1 raw9592step1Labels := by
      have hz : ∀ j, raw9592step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9592step1 = (fun i j => raw9592step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9592step1 raw9592step0; decide +kernel
      have hl : raw9592step1Labels = raw9592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9592step0 raw9592step0Labels permutation80 hz
    mixedMoment B raw9592step1 raw9592step1Labels = mixedMoment B raw9592step2 raw9592step2Labels := by
      have ha : raw9592step2 = (fun i j => raw9592step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9592step2 raw9592step1; decide +kernel
      have hl : raw9592step2Labels = raw9592step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9592step1 raw9592step1Labels permutation31 permutation3
    mixedMoment B raw9592step2 raw9592step2Labels = mixedMoment B raw9592step3 raw9592step3Labels := by
      have ha : raw9592step3 = -raw9592step2 := by apply Matrix.ext; change ∀ i j, raw9592step3 i j = -(raw9592step2 i j); unfold raw9592step3 raw9592step2; decide +kernel
      have hl : raw9592step3Labels = raw9592step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9592step3 raw9592step3Labels = mixedMoment B raw9592step4 raw9592step4Labels := by
      have ha : raw9592step4 = raw9592step3 := by apply Matrix.ext; unfold raw9592step4 raw9592step3; decide +kernel
      have hl : raw9592step3Labels = labelEmbedding6 ∘ raw9592step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9592step3 raw9592step3Labels raw9592step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw9593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9593step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9593step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9593 raw9593Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw9593 raw9593Labels = mixedMoment B raw9593step0 raw9593step0Labels := by
      have hz : ∀ j, raw9593 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9593step0 = (fun i j => raw9593 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9593step0 raw9593; decide +kernel
      have hl : raw9593step0Labels = raw9593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9593 raw9593Labels permutation434 hz
    mixedMoment B raw9593step0 raw9593step0Labels = mixedMoment B raw9593step1 raw9593step1Labels := by
      have ha : raw9593step1 = (fun i j => raw9593step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9593step1 raw9593step0; decide +kernel
      have hl : raw9593step1Labels = raw9593step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9593step0 raw9593step0Labels permutation139 permutation5
    mixedMoment B raw9593step1 raw9593step1Labels = mixedMoment B raw9593step2 raw9593step2Labels := by
      have ha : raw9593step2 = raw9593step1 := by apply Matrix.ext; unfold raw9593step2 raw9593step1; decide +kernel
      have hl : raw9593step1Labels = labelEmbedding8 ∘ raw9593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9593step1 raw9593step1Labels raw9593step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw9594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9594step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9594step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9594 raw9594Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw9594 raw9594Labels = mixedMoment B raw9594step0 raw9594step0Labels := by
      have hz : ∀ j, raw9594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9594step0 = (fun i j => raw9594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9594step0 raw9594; decide +kernel
      have hl : raw9594step0Labels = raw9594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9594 raw9594Labels permutation346 hz
    mixedMoment B raw9594step0 raw9594step0Labels = mixedMoment B raw9594step1 raw9594step1Labels := by
      have ha : raw9594step1 = (fun i j => raw9594step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9594step1 raw9594step0; decide +kernel
      have hl : raw9594step1Labels = raw9594step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9594step0 raw9594step0Labels permutation139 permutation5
    mixedMoment B raw9594step1 raw9594step1Labels = mixedMoment B raw9594step2 raw9594step2Labels := by
      have ha : raw9594step2 = raw9594step1 := by apply Matrix.ext; unfold raw9594step2 raw9594step1; decide +kernel
      have hl : raw9594step1Labels = labelEmbedding8 ∘ raw9594step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9594step1 raw9594step1Labels raw9594step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw9595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw9595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9595step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9595step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9595step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9595 raw9595Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw9595 raw9595Labels = mixedMoment B raw9595step0 raw9595step0Labels := by
      have hz : ∀ j, raw9595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9595step0 = (fun i j => raw9595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9595step0 raw9595; decide +kernel
      have hl : raw9595step0Labels = raw9595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9595 raw9595Labels permutation434 hz
    mixedMoment B raw9595step0 raw9595step0Labels = mixedMoment B raw9595step1 raw9595step1Labels := by
      have hz : ∀ j, raw9595step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9595step1 = (fun i j => raw9595step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9595step1 raw9595step0; decide +kernel
      have hl : raw9595step1Labels = raw9595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9595step0 raw9595step0Labels permutation80 hz
    mixedMoment B raw9595step1 raw9595step1Labels = mixedMoment B raw9595step2 raw9595step2Labels := by
      have ha : raw9595step2 = (fun i j => raw9595step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9595step2 raw9595step1; decide +kernel
      have hl : raw9595step2Labels = raw9595step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9595step1 raw9595step1Labels permutation28 permutation5
    mixedMoment B raw9595step2 raw9595step2Labels = mixedMoment B raw9595step3 raw9595step3Labels := by
      have ha : raw9595step3 = raw9595step2 := by apply Matrix.ext; unfold raw9595step3 raw9595step2; decide +kernel
      have hl : raw9595step2Labels = labelEmbedding8 ∘ raw9595step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9595step2 raw9595step2Labels raw9595step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw9596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw9596step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9596 raw9596Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw9596 raw9596Labels = mixedMoment B raw9596step0 raw9596step0Labels := by
      have hz : ∀ j, raw9596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9596step0 = (fun i j => raw9596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9596step0 raw9596; decide +kernel
      have hl : raw9596step0Labels = raw9596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9596 raw9596Labels permutation434 hz
    mixedMoment B raw9596step0 raw9596step0Labels = mixedMoment B raw9596step1 raw9596step1Labels := by
      have hz : ∀ j, raw9596step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9596step1 = (fun i j => raw9596step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9596step1 raw9596step0; decide +kernel
      have hl : raw9596step1Labels = raw9596step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9596step0 raw9596step0Labels permutation80 hz
    mixedMoment B raw9596step1 raw9596step1Labels = mixedMoment B raw9596step2 raw9596step2Labels := by
      have ha : raw9596step2 = (fun i j => raw9596step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9596step2 raw9596step1; decide +kernel
      have hl : raw9596step2Labels = raw9596step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9596step1 raw9596step1Labels permutation9 permutation2
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw9597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9597step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9597step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9597 raw9597Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw9597 raw9597Labels = mixedMoment B raw9597step0 raw9597step0Labels := by
      have hz : ∀ j, raw9597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9597step0 = (fun i j => raw9597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9597step0 raw9597; decide +kernel
      have hl : raw9597step0Labels = raw9597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9597 raw9597Labels permutation434 hz
    mixedMoment B raw9597step0 raw9597step0Labels = mixedMoment B raw9597step1 raw9597step1Labels := by
      have hz : ∀ j, raw9597step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9597step1 = (fun i j => raw9597step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9597step1 raw9597step0; decide +kernel
      have hl : raw9597step1Labels = raw9597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9597step0 raw9597step0Labels permutation80 hz
    mixedMoment B raw9597step1 raw9597step1Labels = mixedMoment B raw9597step2 raw9597step2Labels := by
      have ha : raw9597step2 = (fun i j => raw9597step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9597step2 raw9597step1; decide +kernel
      have hl : raw9597step2Labels = raw9597step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9597step1 raw9597step1Labels permutation10 permutation3
    mixedMoment B raw9597step2 raw9597step2Labels = mixedMoment B raw9597step3 raw9597step3Labels := by
      have ha : raw9597step3 = raw9597step2 := by apply Matrix.ext; unfold raw9597step3 raw9597step2; decide +kernel
      have hl : raw9597step2Labels = labelEmbedding6 ∘ raw9597step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9597step2 raw9597step2Labels raw9597step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

def raw9598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9598step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9598step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9598 raw9598Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw9598 raw9598Labels = mixedMoment B raw9598step0 raw9598step0Labels := by
      have hz : ∀ j, raw9598 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9598step0 = (fun i j => raw9598 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9598step0 raw9598; decide +kernel
      have hl : raw9598step0Labels = raw9598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9598 raw9598Labels permutation434 hz
    mixedMoment B raw9598step0 raw9598step0Labels = mixedMoment B raw9598step1 raw9598step1Labels := by
      have ha : raw9598step1 = (fun i j => raw9598step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9598step1 raw9598step0; decide +kernel
      have hl : raw9598step1Labels = raw9598step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9598step0 raw9598step0Labels permutation40 permutation3
    mixedMoment B raw9598step1 raw9598step1Labels = mixedMoment B raw9598step2 raw9598step2Labels := by
      have ha : raw9598step2 = raw9598step1 := by apply Matrix.ext; unfold raw9598step2 raw9598step1; decide +kernel
      have hl : raw9598step1Labels = labelEmbedding6 ∘ raw9598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9598step1 raw9598step1Labels raw9598step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw9599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9599step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9599 raw9599Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw9599 raw9599Labels = mixedMoment B raw9599step0 raw9599step0Labels := by
      have hz : ∀ j, raw9599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9599step0 = (fun i j => raw9599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9599step0 raw9599; decide +kernel
      have hl : raw9599step0Labels = raw9599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9599 raw9599Labels permutation346 hz
    mixedMoment B raw9599step0 raw9599step0Labels = mixedMoment B raw9599step1 raw9599step1Labels := by
      have ha : raw9599step1 = (fun i j => raw9599step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9599step1 raw9599step0; decide +kernel
      have hl : raw9599step1Labels = raw9599step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9599step0 raw9599step0Labels permutation40 permutation3
    mixedMoment B raw9599step1 raw9599step1Labels = mixedMoment B raw9599step2 raw9599step2Labels := by
      have ha : raw9599step2 = raw9599step1 := by apply Matrix.ext; unfold raw9599step2 raw9599step1; decide +kernel
      have hl : raw9599step1Labels = labelEmbedding6 ∘ raw9599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9599step1 raw9599step1Labels raw9599step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
