import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14720 raw14720Labels = mixedMoment B node5154 node5154Labels := by
  calc
    mixedMoment B raw14720 raw14720Labels = mixedMoment B raw14720step0 raw14720step0Labels := by
      have ha : raw14720step0 = (fun i j => raw14720 (permutation627 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14720step0 raw14720; decide +kernel
      have hl : raw14720step0Labels = raw14720Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14720 raw14720Labels permutation627 permutation2
    _ = mixedMoment B node5154 node5154Labels := by rfl

def raw14721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw14721step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw14721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14721 raw14721Labels = mixedMoment B node5052 node5052Labels := by
  calc
    mixedMoment B raw14721 raw14721Labels = mixedMoment B raw14721step0 raw14721step0Labels := by
      have ha : raw14721step0 = (fun i j => raw14721 (permutation559 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14721step0 raw14721; decide +kernel
      have hl : raw14721step0Labels = raw14721Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14721 raw14721Labels permutation559 permutation5
    mixedMoment B raw14721step0 raw14721step0Labels = mixedMoment B raw14721step1 raw14721step1Labels := by
      have ha : raw14721step1 = raw14721step0 := by apply Matrix.ext; unfold raw14721step1 raw14721step0; decide +kernel
      have hl : raw14721step0Labels = labelEmbedding8 ∘ raw14721step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14721step0 raw14721step0Labels raw14721step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5052 node5052Labels := by rfl

def raw14722 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14722step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14722 raw14722Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw14722 raw14722Labels = mixedMoment B raw14722step0 raw14722step0Labels := by
      have ha : raw14722step0 = (fun i j => raw14722 (permutation566 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14722step0 raw14722; decide +kernel
      have hl : raw14722step0Labels = raw14722Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14722 raw14722Labels permutation566 permutation5
    mixedMoment B raw14722step0 raw14722step0Labels = mixedMoment B raw14722step1 raw14722step1Labels := by
      have ha : raw14722step1 = raw14722step0 := by apply Matrix.ext; unfold raw14722step1 raw14722step0; decide +kernel
      have hl : raw14722step0Labels = labelEmbedding8 ∘ raw14722step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14722step0 raw14722step0Labels raw14722step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw14723 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14723step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14723 raw14723Labels = mixedMoment B node5053 node5053Labels := by
  calc
    mixedMoment B raw14723 raw14723Labels = mixedMoment B raw14723step0 raw14723step0Labels := by
      have ha : raw14723step0 = (fun i j => raw14723 (permutation558 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14723step0 raw14723; decide +kernel
      have hl : raw14723step0Labels = raw14723Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14723 raw14723Labels permutation558 permutation5
    mixedMoment B raw14723step0 raw14723step0Labels = mixedMoment B raw14723step1 raw14723step1Labels := by
      have ha : raw14723step1 = raw14723step0 := by apply Matrix.ext; unfold raw14723step1 raw14723step0; decide +kernel
      have hl : raw14723step0Labels = labelEmbedding8 ∘ raw14723step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14723step0 raw14723step0Labels raw14723step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5053 node5053Labels := by rfl

def raw14724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14724step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14724 raw14724Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw14724 raw14724Labels = mixedMoment B raw14724step0 raw14724step0Labels := by
      have hz : ∀ j, raw14724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14724step0 = (fun i j => raw14724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14724step0 raw14724; decide +kernel
      have hl : raw14724step0Labels = raw14724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14724 raw14724Labels permutation434 hz
    mixedMoment B raw14724step0 raw14724step0Labels = mixedMoment B raw14724step1 raw14724step1Labels := by
      have ha : raw14724step1 = (fun i j => raw14724step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14724step1 raw14724step0; decide +kernel
      have hl : raw14724step1Labels = raw14724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14724step0 raw14724step0Labels permutation115 permutation5
    mixedMoment B raw14724step1 raw14724step1Labels = mixedMoment B raw14724step2 raw14724step2Labels := by
      have ha : raw14724step2 = raw14724step1 := by apply Matrix.ext; unfold raw14724step2 raw14724step1; decide +kernel
      have hl : raw14724step1Labels = labelEmbedding8 ∘ raw14724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14724step1 raw14724step1Labels raw14724step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw14725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw14725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw14725step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw14725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14725 raw14725Labels = mixedMoment B node5060 node5060Labels := by
  calc
    mixedMoment B raw14725 raw14725Labels = mixedMoment B raw14725step0 raw14725step0Labels := by
      have ha : raw14725step0 = (fun i j => raw14725 (permutation557 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14725step0 raw14725; decide +kernel
      have hl : raw14725step0Labels = raw14725Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14725 raw14725Labels permutation557 permutation5
    mixedMoment B raw14725step0 raw14725step0Labels = mixedMoment B raw14725step1 raw14725step1Labels := by
      have ha : raw14725step1 = raw14725step0 := by apply Matrix.ext; unfold raw14725step1 raw14725step0; decide +kernel
      have hl : raw14725step0Labels = labelEmbedding8 ∘ raw14725step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14725step0 raw14725step0Labels raw14725step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5060 node5060Labels := by rfl

def raw14726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw14726step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14726step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14726step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14726 raw14726Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw14726 raw14726Labels = mixedMoment B raw14726step0 raw14726step0Labels := by
      have ha : raw14726step0 = (fun i j => raw14726 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14726step0 raw14726; decide +kernel
      have hl : raw14726step0Labels = raw14726Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14726 raw14726Labels permutation177 permutation4
    mixedMoment B raw14726step0 raw14726step0Labels = mixedMoment B raw14726step1 raw14726step1Labels := by
      have ha : raw14726step1 = -raw14726step0 := by apply Matrix.ext; change ∀ i j, raw14726step1 i j = -(raw14726step0 i j); unfold raw14726step1 raw14726step0; decide +kernel
      have hl : raw14726step1Labels = raw14726step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14726step1 raw14726step1Labels = mixedMoment B raw14726step2 raw14726step2Labels := by
      have ha : raw14726step2 = raw14726step1 := by apply Matrix.ext; unfold raw14726step2 raw14726step1; decide +kernel
      have hl : raw14726step1Labels = labelEmbedding7 ∘ raw14726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14726step1 raw14726step1Labels raw14726step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5135 node5135Labels := by rfl

def raw14727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw14727step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14727step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14727step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14727step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14727 raw14727Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw14727 raw14727Labels = mixedMoment B raw14727step0 raw14727step0Labels := by
      have ha : raw14727step0 = (fun i j => raw14727 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14727step0 raw14727; decide +kernel
      have hl : raw14727step0Labels = raw14727Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14727 raw14727Labels permutation153 permutation4
    mixedMoment B raw14727step0 raw14727step0Labels = mixedMoment B raw14727step1 raw14727step1Labels := by
      have ha : raw14727step1 = -raw14727step0 := by apply Matrix.ext; change ∀ i j, raw14727step1 i j = -(raw14727step0 i j); unfold raw14727step1 raw14727step0; decide +kernel
      have hl : raw14727step1Labels = raw14727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14727step1 raw14727step1Labels = mixedMoment B raw14727step2 raw14727step2Labels := by
      have ha : raw14727step2 = raw14727step1 := by apply Matrix.ext; unfold raw14727step2 raw14727step1; decide +kernel
      have hl : raw14727step1Labels = labelEmbedding7 ∘ raw14727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14727step1 raw14727step1Labels raw14727step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw14728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw14728step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14728step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14728step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14728step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14728 raw14728Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw14728 raw14728Labels = mixedMoment B raw14728step0 raw14728step0Labels := by
      have ha : raw14728step0 = (fun i j => raw14728 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14728step0 raw14728; decide +kernel
      have hl : raw14728step0Labels = raw14728Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14728 raw14728Labels permutation177 permutation4
    mixedMoment B raw14728step0 raw14728step0Labels = mixedMoment B raw14728step1 raw14728step1Labels := by
      have ha : raw14728step1 = -raw14728step0 := by apply Matrix.ext; change ∀ i j, raw14728step1 i j = -(raw14728step0 i j); unfold raw14728step1 raw14728step0; decide +kernel
      have hl : raw14728step1Labels = raw14728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14728step1 raw14728step1Labels = mixedMoment B raw14728step2 raw14728step2Labels := by
      have ha : raw14728step2 = raw14728step1 := by apply Matrix.ext; unfold raw14728step2 raw14728step1; decide +kernel
      have hl : raw14728step1Labels = labelEmbedding7 ∘ raw14728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14728step1 raw14728step1Labels raw14728step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw14729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14729step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14729step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14729 raw14729Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw14729 raw14729Labels = mixedMoment B raw14729step0 raw14729step0Labels := by
      have hz : ∀ j, raw14729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14729step0 = (fun i j => raw14729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14729step0 raw14729; decide +kernel
      have hl : raw14729step0Labels = raw14729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14729 raw14729Labels permutation434 hz
    mixedMoment B raw14729step0 raw14729step0Labels = mixedMoment B raw14729step1 raw14729step1Labels := by
      have ha : raw14729step1 = (fun i j => raw14729step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14729step1 raw14729step0; decide +kernel
      have hl : raw14729step1Labels = raw14729step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14729step0 raw14729step0Labels permutation39 permutation4
    mixedMoment B raw14729step1 raw14729step1Labels = mixedMoment B raw14729step2 raw14729step2Labels := by
      have ha : raw14729step2 = -raw14729step1 := by apply Matrix.ext; change ∀ i j, raw14729step2 i j = -(raw14729step1 i j); unfold raw14729step2 raw14729step1; decide +kernel
      have hl : raw14729step2Labels = raw14729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14729step2 raw14729step2Labels = mixedMoment B raw14729step3 raw14729step3Labels := by
      have ha : raw14729step3 = raw14729step2 := by apply Matrix.ext; unfold raw14729step3 raw14729step2; decide +kernel
      have hl : raw14729step2Labels = labelEmbedding7 ∘ raw14729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14729step2 raw14729step2Labels raw14729step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw14730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw14730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14730step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14730step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14730 raw14730Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw14730 raw14730Labels = mixedMoment B raw14730step0 raw14730step0Labels := by
      have ha : raw14730step0 = (fun i j => raw14730 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14730step0 raw14730; decide +kernel
      have hl : raw14730step0Labels = raw14730Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14730 raw14730Labels permutation152 permutation6
    mixedMoment B raw14730step0 raw14730step0Labels = mixedMoment B raw14730step1 raw14730step1Labels := by
      have ha : raw14730step1 = raw14730step0 := by apply Matrix.ext; unfold raw14730step1 raw14730step0; decide +kernel
      have hl : raw14730step0Labels = labelEmbedding9 ∘ raw14730step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14730step0 raw14730step0Labels raw14730step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw14731 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14731 raw14731Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw14731 raw14731Labels = mixedMoment B raw14731step0 raw14731step0Labels := by
      have ha : raw14731step0 = (fun i j => raw14731 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14731step0 raw14731; decide +kernel
      have hl : raw14731step0Labels = raw14731Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14731 raw14731Labels permutation152 permutation6
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw14732 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14732 raw14732Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw14732 raw14732Labels = mixedMoment B raw14732step0 raw14732step0Labels := by
      have ha : raw14732step0 = (fun i j => raw14732 (permutation414 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14732step0 raw14732; decide +kernel
      have hl : raw14732step0Labels = raw14732Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14732 raw14732Labels permutation414 permutation3
    _ = mixedMoment B node3730 node3730Labels := by rfl

def raw14733 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14733step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14733 raw14733Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw14733 raw14733Labels = mixedMoment B raw14733step0 raw14733step0Labels := by
      have hz : ∀ j, raw14733 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14733step0 = (fun i j => raw14733 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14733step0 raw14733; decide +kernel
      have hl : raw14733step0Labels = raw14733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14733 raw14733Labels permutation434 hz
    mixedMoment B raw14733step0 raw14733step0Labels = mixedMoment B raw14733step1 raw14733step1Labels := by
      have ha : raw14733step1 = (fun i j => raw14733step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14733step1 raw14733step0; decide +kernel
      have hl : raw14733step1Labels = raw14733step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14733step0 raw14733step0Labels permutation32 permutation6
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw14734 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14734 raw14734Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw14734 raw14734Labels = mixedMoment B raw14734step0 raw14734step0Labels := by
      have ha : raw14734step0 = (fun i j => raw14734 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14734step0 raw14734; decide +kernel
      have hl : raw14734step0Labels = raw14734Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14734 raw14734Labels permutation152 permutation6
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw14735 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14735 raw14735Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw14735 raw14735Labels = mixedMoment B raw14735step0 raw14735step0Labels := by
      have ha : raw14735step0 = (fun i j => raw14735 (permutation623 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14735step0 raw14735; decide +kernel
      have hl : raw14735step0Labels = raw14735Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14735 raw14735Labels permutation623 permutation3
    _ = mixedMoment B node2951 node2951Labels := by rfl

def raw14736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14736 raw14736Labels = mixedMoment B node3559 node3559Labels := by
  calc
    mixedMoment B raw14736 raw14736Labels = mixedMoment B raw14736step0 raw14736step0Labels := by
      have ha : raw14736step0 = (fun i j => raw14736 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14736step0 raw14736; decide +kernel
      have hl : raw14736step0Labels = raw14736Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14736 raw14736Labels permutation152 permutation6
    _ = mixedMoment B node3559 node3559Labels := by rfl

def raw14737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14737 raw14737Labels = mixedMoment B node3714 node3714Labels := by
  calc
    mixedMoment B raw14737 raw14737Labels = mixedMoment B raw14737step0 raw14737step0Labels := by
      have ha : raw14737step0 = (fun i j => raw14737 (permutation416 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14737step0 raw14737; decide +kernel
      have hl : raw14737step0Labels = raw14737Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14737 raw14737Labels permutation416 permutation3
    _ = mixedMoment B node3714 node3714Labels := by rfl

def raw14738 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14738step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14738 raw14738Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw14738 raw14738Labels = mixedMoment B raw14738step0 raw14738step0Labels := by
      have hz : ∀ j, raw14738 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14738step0 = (fun i j => raw14738 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14738step0 raw14738; decide +kernel
      have hl : raw14738step0Labels = raw14738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14738 raw14738Labels permutation434 hz
    mixedMoment B raw14738step0 raw14738step0Labels = mixedMoment B raw14738step1 raw14738step1Labels := by
      have ha : raw14738step1 = (fun i j => raw14738step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14738step1 raw14738step0; decide +kernel
      have hl : raw14738step1Labels = raw14738step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14738step0 raw14738step0Labels permutation32 permutation6
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw14739 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14739 raw14739Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw14739 raw14739Labels = mixedMoment B raw14739step0 raw14739step0Labels := by
      have ha : raw14739step0 = (fun i j => raw14739 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14739step0 raw14739; decide +kernel
      have hl : raw14739step0Labels = raw14739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14739 raw14739Labels permutation152 permutation6
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw14740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14740 raw14740Labels = mixedMoment B node2909 node2909Labels := by
  calc
    mixedMoment B raw14740 raw14740Labels = mixedMoment B raw14740step0 raw14740step0Labels := by
      have ha : raw14740step0 = (fun i j => raw14740 (permutation626 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14740step0 raw14740; decide +kernel
      have hl : raw14740step0Labels = raw14740Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14740 raw14740Labels permutation626 permutation3
    _ = mixedMoment B node2909 node2909Labels := by rfl

def raw14741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14741step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14741 raw14741Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw14741 raw14741Labels = mixedMoment B raw14741step0 raw14741step0Labels := by
      have hz : ∀ j, raw14741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14741step0 = (fun i j => raw14741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14741step0 raw14741; decide +kernel
      have hl : raw14741step0Labels = raw14741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14741 raw14741Labels permutation346 hz
    mixedMoment B raw14741step0 raw14741step0Labels = mixedMoment B raw14741step1 raw14741step1Labels := by
      have ha : raw14741step1 = (fun i j => raw14741step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14741step1 raw14741step0; decide +kernel
      have hl : raw14741step1Labels = raw14741step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14741step0 raw14741step0Labels permutation32 permutation6
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw14742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14742step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14742 raw14742Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw14742 raw14742Labels = mixedMoment B raw14742step0 raw14742step0Labels := by
      have hz : ∀ j, raw14742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14742step0 = (fun i j => raw14742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14742step0 raw14742; decide +kernel
      have hl : raw14742step0Labels = raw14742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14742 raw14742Labels permutation346 hz
    mixedMoment B raw14742step0 raw14742step0Labels = mixedMoment B raw14742step1 raw14742step1Labels := by
      have ha : raw14742step1 = (fun i j => raw14742step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14742step1 raw14742step0; decide +kernel
      have hl : raw14742step1Labels = raw14742step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14742step0 raw14742step0Labels permutation32 permutation6
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw14743 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14743step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14743step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14743 raw14743Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw14743 raw14743Labels = mixedMoment B raw14743step0 raw14743step0Labels := by
      have hz : ∀ j, raw14743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14743step0 = (fun i j => raw14743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14743step0 raw14743; decide +kernel
      have hl : raw14743step0Labels = raw14743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14743 raw14743Labels permutation434 hz
    mixedMoment B raw14743step0 raw14743step0Labels = mixedMoment B raw14743step1 raw14743step1Labels := by
      have hz : ∀ j, raw14743step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14743step1 = (fun i j => raw14743step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14743step1 raw14743step0; decide +kernel
      have hl : raw14743step1Labels = raw14743step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14743step0 raw14743step0Labels permutation80 hz
    mixedMoment B raw14743step1 raw14743step1Labels = mixedMoment B raw14743step2 raw14743step2Labels := by
      have ha : raw14743step2 = (fun i j => raw14743step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14743step2 raw14743step1; decide +kernel
      have hl : raw14743step2Labels = raw14743step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14743step1 raw14743step1Labels permutation8 permutation6
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw14744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14744step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14744 raw14744Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw14744 raw14744Labels = mixedMoment B raw14744step0 raw14744step0Labels := by
      have hz : ∀ j, raw14744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14744step0 = (fun i j => raw14744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14744step0 raw14744; decide +kernel
      have hl : raw14744step0Labels = raw14744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14744 raw14744Labels permutation346 hz
    mixedMoment B raw14744step0 raw14744step0Labels = mixedMoment B raw14744step1 raw14744step1Labels := by
      have ha : raw14744step1 = (fun i j => raw14744step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14744step1 raw14744step0; decide +kernel
      have hl : raw14744step1Labels = raw14744step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14744step0 raw14744step0Labels permutation32 permutation6
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw14745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14745step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14745 raw14745Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw14745 raw14745Labels = mixedMoment B raw14745step0 raw14745step0Labels := by
      have hz : ∀ j, raw14745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14745step0 = (fun i j => raw14745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14745step0 raw14745; decide +kernel
      have hl : raw14745step0Labels = raw14745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14745 raw14745Labels permutation346 hz
    mixedMoment B raw14745step0 raw14745step0Labels = mixedMoment B raw14745step1 raw14745step1Labels := by
      have ha : raw14745step1 = (fun i j => raw14745step0 (permutation128 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14745step1 raw14745step0; decide +kernel
      have hl : raw14745step1Labels = raw14745step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14745step0 raw14745step0Labels permutation128 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw14746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw14746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14746 raw14746Labels = mixedMoment B node3518 node3518Labels := by
  calc
    mixedMoment B raw14746 raw14746Labels = mixedMoment B raw14746step0 raw14746step0Labels := by
      have ha : raw14746step0 = (fun i j => raw14746 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14746step0 raw14746; decide +kernel
      have hl : raw14746step0Labels = raw14746Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14746 raw14746Labels permutation152 permutation6
    _ = mixedMoment B node3518 node3518Labels := by rfl

def raw14747 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14747 raw14747Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw14747 raw14747Labels = mixedMoment B raw14747step0 raw14747step0Labels := by
      have ha : raw14747step0 = (fun i j => raw14747 (permutation489 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14747step0 raw14747; decide +kernel
      have hl : raw14747step0Labels = raw14747Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14747 raw14747Labels permutation489 permutation3
    mixedMoment B raw14747step0 raw14747step0Labels = mixedMoment B raw14747step1 raw14747step1Labels := by
      have ha : raw14747step1 = -raw14747step0 := by apply Matrix.ext; change ∀ i j, raw14747step1 i j = -(raw14747step0 i j); unfold raw14747step1 raw14747step0; decide +kernel
      have hl : raw14747step1Labels = raw14747step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw14748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14748 raw14748Labels = mixedMoment B node3712 node3712Labels := by
  calc
    mixedMoment B raw14748 raw14748Labels = mixedMoment B raw14748step0 raw14748step0Labels := by
      have ha : raw14748step0 = (fun i j => raw14748 (permutation415 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14748step0 raw14748; decide +kernel
      have hl : raw14748step0Labels = raw14748Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14748 raw14748Labels permutation415 permutation3
    _ = mixedMoment B node3712 node3712Labels := by rfl

def raw14749 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14749 raw14749Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw14749 raw14749Labels = mixedMoment B raw14749step0 raw14749step0Labels := by
      have ha : raw14749step0 = (fun i j => raw14749 (permutation459 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14749step0 raw14749; decide +kernel
      have hl : raw14749step0Labels = raw14749Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14749 raw14749Labels permutation459 permutation3
    mixedMoment B raw14749step0 raw14749step0Labels = mixedMoment B raw14749step1 raw14749step1Labels := by
      have ha : raw14749step1 = -raw14749step0 := by apply Matrix.ext; change ∀ i j, raw14749step1 i j = -(raw14749step0 i j); unfold raw14749step1 raw14749step0; decide +kernel
      have hl : raw14749step1Labels = raw14749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw14750 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14750Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14750 raw14750Labels = mixedMoment B node2907 node2907Labels := by
  calc
    mixedMoment B raw14750 raw14750Labels = mixedMoment B raw14750step0 raw14750step0Labels := by
      have ha : raw14750step0 = (fun i j => raw14750 (permutation624 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14750step0 raw14750; decide +kernel
      have hl : raw14750step0Labels = raw14750Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14750 raw14750Labels permutation624 permutation3
    _ = mixedMoment B node2907 node2907Labels := by rfl

def raw14751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14751Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw14751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw14751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14751 raw14751Labels = mixedMoment B node3437 node3437Labels := by
  calc
    mixedMoment B raw14751 raw14751Labels = mixedMoment B raw14751step0 raw14751step0Labels := by
      have ha : raw14751step0 = (fun i j => raw14751 (permutation556 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14751step0 raw14751; decide +kernel
      have hl : raw14751step0Labels = raw14751Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14751 raw14751Labels permutation556 permutation3
    mixedMoment B raw14751step0 raw14751step0Labels = mixedMoment B raw14751step1 raw14751step1Labels := by
      have ha : raw14751step1 = -raw14751step0 := by apply Matrix.ext; change ∀ i j, raw14751step1 i j = -(raw14751step0 i j); unfold raw14751step1 raw14751step0; decide +kernel
      have hl : raw14751step1Labels = raw14751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3437 node3437Labels := by rfl

def raw14752 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14752Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14752 raw14752Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw14752 raw14752Labels = mixedMoment B raw14752step0 raw14752step0Labels := by
      have ha : raw14752step0 = (fun i j => raw14752 (permutation554 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14752step0 raw14752; decide +kernel
      have hl : raw14752step0Labels = raw14752Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14752 raw14752Labels permutation554 permutation3
    mixedMoment B raw14752step0 raw14752step0Labels = mixedMoment B raw14752step1 raw14752step1Labels := by
      have ha : raw14752step1 = -raw14752step0 := by apply Matrix.ext; change ∀ i j, raw14752step1 i j = -(raw14752step0 i j); unfold raw14752step1 raw14752step0; decide +kernel
      have hl : raw14752step1Labels = raw14752step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw14753 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14753Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw14753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14753 raw14753Labels = mixedMoment B node3430 node3430Labels := by
  calc
    mixedMoment B raw14753 raw14753Labels = mixedMoment B raw14753step0 raw14753step0Labels := by
      have ha : raw14753step0 = (fun i j => raw14753 (permutation555 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14753step0 raw14753; decide +kernel
      have hl : raw14753step0Labels = raw14753Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14753 raw14753Labels permutation555 permutation3
    mixedMoment B raw14753step0 raw14753step0Labels = mixedMoment B raw14753step1 raw14753step1Labels := by
      have ha : raw14753step1 = -raw14753step0 := by apply Matrix.ext; change ∀ i j, raw14753step1 i j = -(raw14753step0 i j); unfold raw14753step1 raw14753step0; decide +kernel
      have hl : raw14753step1Labels = raw14753step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3430 node3430Labels := by rfl

def raw14754 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14754 raw14754Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw14754 raw14754Labels = mixedMoment B raw14754step0 raw14754step0Labels := by
      have hz : ∀ j, raw14754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14754step0 = (fun i j => raw14754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14754step0 raw14754; decide +kernel
      have hl : raw14754step0Labels = raw14754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14754 raw14754Labels permutation434 hz
    mixedMoment B raw14754step0 raw14754step0Labels = mixedMoment B raw14754step1 raw14754step1Labels := by
      have ha : raw14754step1 = (fun i j => raw14754step0 (permutation110 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14754step1 raw14754step0; decide +kernel
      have hl : raw14754step1Labels = raw14754step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14754step0 raw14754step0Labels permutation110 permutation3
    mixedMoment B raw14754step1 raw14754step1Labels = mixedMoment B raw14754step2 raw14754step2Labels := by
      have ha : raw14754step2 = -raw14754step1 := by apply Matrix.ext; change ∀ i j, raw14754step2 i j = -(raw14754step1 i j); unfold raw14754step2 raw14754step1; decide +kernel
      have hl : raw14754step2Labels = raw14754step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw14755 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw14755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14755 raw14755Labels = mixedMoment B node2906 node2906Labels := by
  calc
    mixedMoment B raw14755 raw14755Labels = mixedMoment B raw14755step0 raw14755step0Labels := by
      have ha : raw14755step0 = (fun i j => raw14755 (permutation623 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14755step0 raw14755; decide +kernel
      have hl : raw14755step0Labels = raw14755Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14755 raw14755Labels permutation623 permutation3
    _ = mixedMoment B node2906 node2906Labels := by rfl

def raw14756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14756 raw14756Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw14756 raw14756Labels = mixedMoment B raw14756step0 raw14756step0Labels := by
      have ha : raw14756step0 = (fun i j => raw14756 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14756step0 raw14756; decide +kernel
      have hl : raw14756step0Labels = raw14756Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14756 raw14756Labels permutation152 permutation6
    _ = mixedMoment B node3515 node3515Labels := by rfl

def raw14757 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14757 raw14757Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw14757 raw14757Labels = mixedMoment B raw14757step0 raw14757step0Labels := by
      have ha : raw14757step0 = (fun i j => raw14757 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14757step0 raw14757; decide +kernel
      have hl : raw14757step0Labels = raw14757Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14757 raw14757Labels permutation152 permutation6
    _ = mixedMoment B node3794 node3794Labels := by rfl

def raw14758 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14758 raw14758Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw14758 raw14758Labels = mixedMoment B raw14758step0 raw14758step0Labels := by
      have ha : raw14758step0 = (fun i j => raw14758 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14758step0 raw14758; decide +kernel
      have hl : raw14758step0Labels = raw14758Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14758 raw14758Labels permutation152 permutation6
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw14759 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14759step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14759 raw14759Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw14759 raw14759Labels = mixedMoment B raw14759step0 raw14759step0Labels := by
      have hz : ∀ j, raw14759 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14759step0 = (fun i j => raw14759 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14759step0 raw14759; decide +kernel
      have hl : raw14759step0Labels = raw14759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14759 raw14759Labels permutation434 hz
    mixedMoment B raw14759step0 raw14759step0Labels = mixedMoment B raw14759step1 raw14759step1Labels := by
      have ha : raw14759step1 = (fun i j => raw14759step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14759step1 raw14759step0; decide +kernel
      have hl : raw14759step1Labels = raw14759step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14759step0 raw14759step0Labels permutation32 permutation6
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw14760 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw14760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14760 raw14760Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw14760 raw14760Labels = mixedMoment B raw14760step0 raw14760step0Labels := by
      have ha : raw14760step0 = (fun i j => raw14760 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14760step0 raw14760; decide +kernel
      have hl : raw14760step0Labels = raw14760Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14760 raw14760Labels permutation152 permutation6
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw14761 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14761step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14761step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14761 raw14761Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw14761 raw14761Labels = mixedMoment B raw14761step0 raw14761step0Labels := by
      have ha : raw14761step0 = (fun i j => raw14761 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14761step0 raw14761; decide +kernel
      have hl : raw14761step0Labels = raw14761Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14761 raw14761Labels permutation682 permutation7
    mixedMoment B raw14761step0 raw14761step0Labels = mixedMoment B raw14761step1 raw14761step1Labels := by
      have ha : raw14761step1 = -raw14761step0 := by apply Matrix.ext; change ∀ i j, raw14761step1 i j = -(raw14761step0 i j); unfold raw14761step1 raw14761step0; decide +kernel
      have hl : raw14761step1Labels = raw14761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14761step1 raw14761step1Labels = mixedMoment B raw14761step2 raw14761step2Labels := by
      have ha : raw14761step2 = raw14761step1 := by apply Matrix.ext; unfold raw14761step2 raw14761step1; decide +kernel
      have hl : raw14761step1Labels = labelEmbedding1 ∘ raw14761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14761step1 raw14761step1Labels raw14761step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw14762 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14762step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14762step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14762 raw14762Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw14762 raw14762Labels = mixedMoment B raw14762step0 raw14762step0Labels := by
      have ha : raw14762step0 = (fun i j => raw14762 (permutation361 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14762step0 raw14762; decide +kernel
      have hl : raw14762step0Labels = raw14762Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14762 raw14762Labels permutation361 permutation5
    mixedMoment B raw14762step0 raw14762step0Labels = mixedMoment B raw14762step1 raw14762step1Labels := by
      have ha : raw14762step1 = -raw14762step0 := by apply Matrix.ext; change ∀ i j, raw14762step1 i j = -(raw14762step0 i j); unfold raw14762step1 raw14762step0; decide +kernel
      have hl : raw14762step1Labels = raw14762step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14762step1 raw14762step1Labels = mixedMoment B raw14762step2 raw14762step2Labels := by
      have ha : raw14762step2 = raw14762step1 := by apply Matrix.ext; unfold raw14762step2 raw14762step1; decide +kernel
      have hl : raw14762step1Labels = labelEmbedding1 ∘ raw14762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14762step1 raw14762step1Labels raw14762step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3866 node3866Labels := by rfl

def raw14763 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14763step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14763step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14763 raw14763Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw14763 raw14763Labels = mixedMoment B raw14763step0 raw14763step0Labels := by
      have hz : ∀ j, raw14763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14763step0 = (fun i j => raw14763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14763step0 raw14763; decide +kernel
      have hl : raw14763step0Labels = raw14763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14763 raw14763Labels permutation434 hz
    mixedMoment B raw14763step0 raw14763step0Labels = mixedMoment B raw14763step1 raw14763step1Labels := by
      have ha : raw14763step1 = (fun i j => raw14763step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14763step1 raw14763step0; decide +kernel
      have hl : raw14763step1Labels = raw14763step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14763step0 raw14763step0Labels permutation151 permutation7
    mixedMoment B raw14763step1 raw14763step1Labels = mixedMoment B raw14763step2 raw14763step2Labels := by
      have ha : raw14763step2 = -raw14763step1 := by apply Matrix.ext; change ∀ i j, raw14763step2 i j = -(raw14763step1 i j); unfold raw14763step2 raw14763step1; decide +kernel
      have hl : raw14763step2Labels = raw14763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14763step2 raw14763step2Labels = mixedMoment B raw14763step3 raw14763step3Labels := by
      have ha : raw14763step3 = raw14763step2 := by apply Matrix.ext; unfold raw14763step3 raw14763step2; decide +kernel
      have hl : raw14763step2Labels = labelEmbedding1 ∘ raw14763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14763step2 raw14763step2Labels raw14763step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw14764 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14764step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14764 raw14764Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw14764 raw14764Labels = mixedMoment B raw14764step0 raw14764step0Labels := by
      have ha : raw14764step0 = (fun i j => raw14764 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14764step0 raw14764; decide +kernel
      have hl : raw14764step0Labels = raw14764Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14764 raw14764Labels permutation682 permutation7
    mixedMoment B raw14764step0 raw14764step0Labels = mixedMoment B raw14764step1 raw14764step1Labels := by
      have ha : raw14764step1 = -raw14764step0 := by apply Matrix.ext; change ∀ i j, raw14764step1 i j = -(raw14764step0 i j); unfold raw14764step1 raw14764step0; decide +kernel
      have hl : raw14764step1Labels = raw14764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14764step1 raw14764step1Labels = mixedMoment B raw14764step2 raw14764step2Labels := by
      have ha : raw14764step2 = raw14764step1 := by apply Matrix.ext; unfold raw14764step2 raw14764step1; decide +kernel
      have hl : raw14764step1Labels = labelEmbedding1 ∘ raw14764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14764step1 raw14764step1Labels raw14764step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw14765 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14765step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14765step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14765step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14765 raw14765Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw14765 raw14765Labels = mixedMoment B raw14765step0 raw14765step0Labels := by
      have ha : raw14765step0 = (fun i j => raw14765 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14765step0 raw14765; decide +kernel
      have hl : raw14765step0Labels = raw14765Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14765 raw14765Labels permutation682 permutation7
    mixedMoment B raw14765step0 raw14765step0Labels = mixedMoment B raw14765step1 raw14765step1Labels := by
      have ha : raw14765step1 = -raw14765step0 := by apply Matrix.ext; change ∀ i j, raw14765step1 i j = -(raw14765step0 i j); unfold raw14765step1 raw14765step0; decide +kernel
      have hl : raw14765step1Labels = raw14765step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14765step1 raw14765step1Labels = mixedMoment B raw14765step2 raw14765step2Labels := by
      have ha : raw14765step2 = raw14765step1 := by apply Matrix.ext; unfold raw14765step2 raw14765step1; decide +kernel
      have hl : raw14765step1Labels = labelEmbedding1 ∘ raw14765step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14765step1 raw14765step1Labels raw14765step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw14766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14766step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14766step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14766 raw14766Labels = mixedMoment B node2909 node2909Labels := by
  calc
    mixedMoment B raw14766 raw14766Labels = mixedMoment B raw14766step0 raw14766step0Labels := by
      have ha : raw14766step0 = (fun i j => raw14766 (permutation196 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14766step0 raw14766; decide +kernel
      have hl : raw14766step0Labels = raw14766Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14766 raw14766Labels permutation196 permutation5
    mixedMoment B raw14766step0 raw14766step0Labels = mixedMoment B raw14766step1 raw14766step1Labels := by
      have ha : raw14766step1 = -raw14766step0 := by apply Matrix.ext; change ∀ i j, raw14766step1 i j = -(raw14766step0 i j); unfold raw14766step1 raw14766step0; decide +kernel
      have hl : raw14766step1Labels = raw14766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14766step1 raw14766step1Labels = mixedMoment B raw14766step2 raw14766step2Labels := by
      have ha : raw14766step2 = raw14766step1 := by apply Matrix.ext; unfold raw14766step2 raw14766step1; decide +kernel
      have hl : raw14766step1Labels = labelEmbedding1 ∘ raw14766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14766step1 raw14766step1Labels raw14766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2909 node2909Labels := by rfl

def raw14767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14767step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14767step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14767step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14767step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14767 raw14767Labels = mixedMoment B node3714 node3714Labels := by
  calc
    mixedMoment B raw14767 raw14767Labels = mixedMoment B raw14767step0 raw14767step0Labels := by
      have ha : raw14767step0 = (fun i j => raw14767 (permutation363 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14767step0 raw14767; decide +kernel
      have hl : raw14767step0Labels = raw14767Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14767 raw14767Labels permutation363 permutation5
    mixedMoment B raw14767step0 raw14767step0Labels = mixedMoment B raw14767step1 raw14767step1Labels := by
      have ha : raw14767step1 = -raw14767step0 := by apply Matrix.ext; change ∀ i j, raw14767step1 i j = -(raw14767step0 i j); unfold raw14767step1 raw14767step0; decide +kernel
      have hl : raw14767step1Labels = raw14767step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14767step1 raw14767step1Labels = mixedMoment B raw14767step2 raw14767step2Labels := by
      have ha : raw14767step2 = raw14767step1 := by apply Matrix.ext; unfold raw14767step2 raw14767step1; decide +kernel
      have hl : raw14767step1Labels = labelEmbedding1 ∘ raw14767step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14767step1 raw14767step1Labels raw14767step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3714 node3714Labels := by rfl

def raw14768 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14768step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14768step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14768step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14768step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14768 raw14768Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw14768 raw14768Labels = mixedMoment B raw14768step0 raw14768step0Labels := by
      have hz : ∀ j, raw14768 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14768step0 = (fun i j => raw14768 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14768step0 raw14768; decide +kernel
      have hl : raw14768step0Labels = raw14768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14768 raw14768Labels permutation434 hz
    mixedMoment B raw14768step0 raw14768step0Labels = mixedMoment B raw14768step1 raw14768step1Labels := by
      have ha : raw14768step1 = (fun i j => raw14768step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14768step1 raw14768step0; decide +kernel
      have hl : raw14768step1Labels = raw14768step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14768step0 raw14768step0Labels permutation151 permutation7
    mixedMoment B raw14768step1 raw14768step1Labels = mixedMoment B raw14768step2 raw14768step2Labels := by
      have ha : raw14768step2 = -raw14768step1 := by apply Matrix.ext; change ∀ i j, raw14768step2 i j = -(raw14768step1 i j); unfold raw14768step2 raw14768step1; decide +kernel
      have hl : raw14768step2Labels = raw14768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14768step2 raw14768step2Labels = mixedMoment B raw14768step3 raw14768step3Labels := by
      have ha : raw14768step3 = raw14768step2 := by apply Matrix.ext; unfold raw14768step3 raw14768step2; decide +kernel
      have hl : raw14768step2Labels = labelEmbedding1 ∘ raw14768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14768step2 raw14768step2Labels raw14768step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw14769 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14769step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14769step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14769step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14769 raw14769Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw14769 raw14769Labels = mixedMoment B raw14769step0 raw14769step0Labels := by
      have ha : raw14769step0 = (fun i j => raw14769 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14769step0 raw14769; decide +kernel
      have hl : raw14769step0Labels = raw14769Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14769 raw14769Labels permutation682 permutation7
    mixedMoment B raw14769step0 raw14769step0Labels = mixedMoment B raw14769step1 raw14769step1Labels := by
      have ha : raw14769step1 = -raw14769step0 := by apply Matrix.ext; change ∀ i j, raw14769step1 i j = -(raw14769step0 i j); unfold raw14769step1 raw14769step0; decide +kernel
      have hl : raw14769step1Labels = raw14769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14769step1 raw14769step1Labels = mixedMoment B raw14769step2 raw14769step2Labels := by
      have ha : raw14769step2 = raw14769step1 := by apply Matrix.ext; unfold raw14769step2 raw14769step1; decide +kernel
      have hl : raw14769step1Labels = labelEmbedding1 ∘ raw14769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14769step1 raw14769step1Labels raw14769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw14770 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14770step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14770step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14770 raw14770Labels = mixedMoment B node3559 node3559Labels := by
  calc
    mixedMoment B raw14770 raw14770Labels = mixedMoment B raw14770step0 raw14770step0Labels := by
      have ha : raw14770step0 = (fun i j => raw14770 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14770step0 raw14770; decide +kernel
      have hl : raw14770step0Labels = raw14770Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14770 raw14770Labels permutation682 permutation7
    mixedMoment B raw14770step0 raw14770step0Labels = mixedMoment B raw14770step1 raw14770step1Labels := by
      have ha : raw14770step1 = -raw14770step0 := by apply Matrix.ext; change ∀ i j, raw14770step1 i j = -(raw14770step0 i j); unfold raw14770step1 raw14770step0; decide +kernel
      have hl : raw14770step1Labels = raw14770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14770step1 raw14770step1Labels = mixedMoment B raw14770step2 raw14770step2Labels := by
      have ha : raw14770step2 = raw14770step1 := by apply Matrix.ext; unfold raw14770step2 raw14770step1; decide +kernel
      have hl : raw14770step1Labels = labelEmbedding1 ∘ raw14770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14770step1 raw14770step1Labels raw14770step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3559 node3559Labels := by rfl

def raw14771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14771step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14771step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14771step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14771step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14771step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14771 raw14771Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw14771 raw14771Labels = mixedMoment B raw14771step0 raw14771step0Labels := by
      have hz : ∀ j, raw14771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14771step0 = (fun i j => raw14771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14771step0 raw14771; decide +kernel
      have hl : raw14771step0Labels = raw14771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14771 raw14771Labels permutation346 hz
    mixedMoment B raw14771step0 raw14771step0Labels = mixedMoment B raw14771step1 raw14771step1Labels := by
      have ha : raw14771step1 = (fun i j => raw14771step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14771step1 raw14771step0; decide +kernel
      have hl : raw14771step1Labels = raw14771step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14771step0 raw14771step0Labels permutation50 permutation5
    mixedMoment B raw14771step1 raw14771step1Labels = mixedMoment B raw14771step2 raw14771step2Labels := by
      have ha : raw14771step2 = -raw14771step1 := by apply Matrix.ext; change ∀ i j, raw14771step2 i j = -(raw14771step1 i j); unfold raw14771step2 raw14771step1; decide +kernel
      have hl : raw14771step2Labels = raw14771step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14771step2 raw14771step2Labels = mixedMoment B raw14771step3 raw14771step3Labels := by
      have ha : raw14771step3 = raw14771step2 := by apply Matrix.ext; unfold raw14771step3 raw14771step2; decide +kernel
      have hl : raw14771step2Labels = labelEmbedding1 ∘ raw14771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14771step2 raw14771step2Labels raw14771step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw14772 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14772step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw14772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14772step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14772step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14772step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14772 raw14772Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw14772 raw14772Labels = mixedMoment B raw14772step0 raw14772step0Labels := by
      have hz : ∀ j, raw14772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14772step0 = (fun i j => raw14772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14772step0 raw14772; decide +kernel
      have hl : raw14772step0Labels = raw14772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14772 raw14772Labels permutation346 hz
    mixedMoment B raw14772step0 raw14772step0Labels = mixedMoment B raw14772step1 raw14772step1Labels := by
      have ha : raw14772step1 = (fun i j => raw14772step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14772step1 raw14772step0; decide +kernel
      have hl : raw14772step1Labels = raw14772step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14772step0 raw14772step0Labels permutation151 permutation7
    mixedMoment B raw14772step1 raw14772step1Labels = mixedMoment B raw14772step2 raw14772step2Labels := by
      have ha : raw14772step2 = -raw14772step1 := by apply Matrix.ext; change ∀ i j, raw14772step2 i j = -(raw14772step1 i j); unfold raw14772step2 raw14772step1; decide +kernel
      have hl : raw14772step2Labels = raw14772step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14772step2 raw14772step2Labels = mixedMoment B raw14772step3 raw14772step3Labels := by
      have ha : raw14772step3 = raw14772step2 := by apply Matrix.ext; unfold raw14772step3 raw14772step2; decide +kernel
      have hl : raw14772step2Labels = labelEmbedding1 ∘ raw14772step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14772step2 raw14772step2Labels raw14772step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw14773 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14773step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14773step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14773step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14773step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14773step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14773step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14773step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14773 raw14773Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw14773 raw14773Labels = mixedMoment B raw14773step0 raw14773step0Labels := by
      have hz : ∀ j, raw14773 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14773step0 = (fun i j => raw14773 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14773step0 raw14773; decide +kernel
      have hl : raw14773step0Labels = raw14773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14773 raw14773Labels permutation434 hz
    mixedMoment B raw14773step0 raw14773step0Labels = mixedMoment B raw14773step1 raw14773step1Labels := by
      have hz : ∀ j, raw14773step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14773step1 = (fun i j => raw14773step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14773step1 raw14773step0; decide +kernel
      have hl : raw14773step1Labels = raw14773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14773step0 raw14773step0Labels permutation80 hz
    mixedMoment B raw14773step1 raw14773step1Labels = mixedMoment B raw14773step2 raw14773step2Labels := by
      have ha : raw14773step2 = (fun i j => raw14773step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14773step2 raw14773step1; decide +kernel
      have hl : raw14773step2Labels = raw14773step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14773step1 raw14773step1Labels permutation31 permutation7
    mixedMoment B raw14773step2 raw14773step2Labels = mixedMoment B raw14773step3 raw14773step3Labels := by
      have ha : raw14773step3 = -raw14773step2 := by apply Matrix.ext; change ∀ i j, raw14773step3 i j = -(raw14773step2 i j); unfold raw14773step3 raw14773step2; decide +kernel
      have hl : raw14773step3Labels = raw14773step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14773step3 raw14773step3Labels = mixedMoment B raw14773step4 raw14773step4Labels := by
      have ha : raw14773step4 = raw14773step3 := by apply Matrix.ext; unfold raw14773step4 raw14773step3; decide +kernel
      have hl : raw14773step3Labels = labelEmbedding1 ∘ raw14773step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14773step3 raw14773step3Labels raw14773step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw14774 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14774step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14774step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14774step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14774step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14774step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14774 raw14774Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw14774 raw14774Labels = mixedMoment B raw14774step0 raw14774step0Labels := by
      have hz : ∀ j, raw14774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14774step0 = (fun i j => raw14774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14774step0 raw14774; decide +kernel
      have hl : raw14774step0Labels = raw14774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14774 raw14774Labels permutation346 hz
    mixedMoment B raw14774step0 raw14774step0Labels = mixedMoment B raw14774step1 raw14774step1Labels := by
      have ha : raw14774step1 = (fun i j => raw14774step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14774step1 raw14774step0; decide +kernel
      have hl : raw14774step1Labels = raw14774step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14774step0 raw14774step0Labels permutation151 permutation7
    mixedMoment B raw14774step1 raw14774step1Labels = mixedMoment B raw14774step2 raw14774step2Labels := by
      have ha : raw14774step2 = -raw14774step1 := by apply Matrix.ext; change ∀ i j, raw14774step2 i j = -(raw14774step1 i j); unfold raw14774step2 raw14774step1; decide +kernel
      have hl : raw14774step2Labels = raw14774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14774step2 raw14774step2Labels = mixedMoment B raw14774step3 raw14774step3Labels := by
      have ha : raw14774step3 = raw14774step2 := by apply Matrix.ext; unfold raw14774step3 raw14774step2; decide +kernel
      have hl : raw14774step2Labels = labelEmbedding1 ∘ raw14774step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14774step2 raw14774step2Labels raw14774step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw14775 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14775step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14775step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14775step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14775step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14775 raw14775Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw14775 raw14775Labels = mixedMoment B raw14775step0 raw14775step0Labels := by
      have hz : ∀ j, raw14775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14775step0 = (fun i j => raw14775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14775step0 raw14775; decide +kernel
      have hl : raw14775step0Labels = raw14775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14775 raw14775Labels permutation346 hz
    mixedMoment B raw14775step0 raw14775step0Labels = mixedMoment B raw14775step1 raw14775step1Labels := by
      have ha : raw14775step1 = (fun i j => raw14775step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14775step1 raw14775step0; decide +kernel
      have hl : raw14775step1Labels = raw14775step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14775step0 raw14775step0Labels permutation151 permutation7
    mixedMoment B raw14775step1 raw14775step1Labels = mixedMoment B raw14775step2 raw14775step2Labels := by
      have ha : raw14775step2 = -raw14775step1 := by apply Matrix.ext; change ∀ i j, raw14775step2 i j = -(raw14775step1 i j); unfold raw14775step2 raw14775step1; decide +kernel
      have hl : raw14775step2Labels = raw14775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14775step2 raw14775step2Labels = mixedMoment B raw14775step3 raw14775step3Labels := by
      have ha : raw14775step3 = raw14775step2 := by apply Matrix.ext; unfold raw14775step3 raw14775step2; decide +kernel
      have hl : raw14775step2Labels = labelEmbedding1 ∘ raw14775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14775step2 raw14775step2Labels raw14775step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw14776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 2, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw14776step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14776step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14776step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14776step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14776 raw14776Labels = mixedMoment B node2905 node2905Labels := by
  calc
    mixedMoment B raw14776 raw14776Labels = mixedMoment B raw14776step0 raw14776step0Labels := by
      have ha : raw14776step0 = (fun i j => raw14776 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14776step0 raw14776; decide +kernel
      have hl : raw14776step0Labels = raw14776Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14776 raw14776Labels permutation195 permutation5
    mixedMoment B raw14776step0 raw14776step0Labels = mixedMoment B raw14776step1 raw14776step1Labels := by
      have ha : raw14776step1 = -raw14776step0 := by apply Matrix.ext; change ∀ i j, raw14776step1 i j = -(raw14776step0 i j); unfold raw14776step1 raw14776step0; decide +kernel
      have hl : raw14776step1Labels = raw14776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14776step1 raw14776step1Labels = mixedMoment B raw14776step2 raw14776step2Labels := by
      have ha : raw14776step2 = raw14776step1 := by apply Matrix.ext; unfold raw14776step2 raw14776step1; decide +kernel
      have hl : raw14776step1Labels = labelEmbedding1 ∘ raw14776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14776step1 raw14776step1Labels raw14776step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2905 node2905Labels := by rfl

def raw14777 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14777step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14777step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14777step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14777 raw14777Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw14777 raw14777Labels = mixedMoment B raw14777step0 raw14777step0Labels := by
      have ha : raw14777step0 = (fun i j => raw14777 (permutation502 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14777step0 raw14777; decide +kernel
      have hl : raw14777step0Labels = raw14777Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14777 raw14777Labels permutation502 permutation5
    mixedMoment B raw14777step0 raw14777step0Labels = mixedMoment B raw14777step1 raw14777step1Labels := by
      have ha : raw14777step1 = raw14777step0 := by apply Matrix.ext; unfold raw14777step1 raw14777step0; decide +kernel
      have hl : raw14777step0Labels = labelEmbedding1 ∘ raw14777step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14777step0 raw14777step0Labels raw14777step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3698 node3698Labels := by rfl

def raw14778 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14778step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14778 raw14778Labels = mixedMoment B node3679 node3679Labels := by
  calc
    mixedMoment B raw14778 raw14778Labels = mixedMoment B raw14778step0 raw14778step0Labels := by
      have ha : raw14778step0 = (fun i j => raw14778 (permutation493 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14778step0 raw14778; decide +kernel
      have hl : raw14778step0Labels = raw14778Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14778 raw14778Labels permutation493 permutation5
    mixedMoment B raw14778step0 raw14778step0Labels = mixedMoment B raw14778step1 raw14778step1Labels := by
      have ha : raw14778step1 = raw14778step0 := by apply Matrix.ext; unfold raw14778step1 raw14778step0; decide +kernel
      have hl : raw14778step0Labels = labelEmbedding1 ∘ raw14778step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14778step0 raw14778step0Labels raw14778step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3679 node3679Labels := by rfl

def raw14779 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14779step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14779 raw14779Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw14779 raw14779Labels = mixedMoment B raw14779step0 raw14779step0Labels := by
      have ha : raw14779step0 = (fun i j => raw14779 (permutation494 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14779step0 raw14779; decide +kernel
      have hl : raw14779step0Labels = raw14779Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14779 raw14779Labels permutation494 permutation5
    mixedMoment B raw14779step0 raw14779step0Labels = mixedMoment B raw14779step1 raw14779step1Labels := by
      have ha : raw14779step1 = raw14779step0 := by apply Matrix.ext; unfold raw14779step1 raw14779step0; decide +kernel
      have hl : raw14779step0Labels = labelEmbedding1 ∘ raw14779step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14779step0 raw14779step0Labels raw14779step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw14780 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14780step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14780step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14780step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14780step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14780 raw14780Labels = mixedMoment B node3561 node3561Labels := by
  calc
    mixedMoment B raw14780 raw14780Labels = mixedMoment B raw14780step0 raw14780step0Labels := by
      have ha : raw14780step0 = (fun i j => raw14780 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14780step0 raw14780; decide +kernel
      have hl : raw14780step0Labels = raw14780Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14780 raw14780Labels permutation682 permutation7
    mixedMoment B raw14780step0 raw14780step0Labels = mixedMoment B raw14780step1 raw14780step1Labels := by
      have ha : raw14780step1 = -raw14780step0 := by apply Matrix.ext; change ∀ i j, raw14780step1 i j = -(raw14780step0 i j); unfold raw14780step1 raw14780step0; decide +kernel
      have hl : raw14780step1Labels = raw14780step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14780step1 raw14780step1Labels = mixedMoment B raw14780step2 raw14780step2Labels := by
      have ha : raw14780step2 = raw14780step1 := by apply Matrix.ext; unfold raw14780step2 raw14780step1; decide +kernel
      have hl : raw14780step1Labels = labelEmbedding1 ∘ raw14780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14780step1 raw14780step1Labels raw14780step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3561 node3561Labels := by rfl

def raw14781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw14781step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw14781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14781 raw14781Labels = mixedMoment B node2454 node2454Labels := by
  calc
    mixedMoment B raw14781 raw14781Labels = mixedMoment B raw14781step0 raw14781step0Labels := by
      have ha : raw14781step0 = (fun i j => raw14781 (permutation559 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14781step0 raw14781; decide +kernel
      have hl : raw14781step0Labels = raw14781Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14781 raw14781Labels permutation559 permutation5
    mixedMoment B raw14781step0 raw14781step0Labels = mixedMoment B raw14781step1 raw14781step1Labels := by
      have ha : raw14781step1 = raw14781step0 := by apply Matrix.ext; unfold raw14781step1 raw14781step0; decide +kernel
      have hl : raw14781step0Labels = labelEmbedding1 ∘ raw14781step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14781step0 raw14781step0Labels raw14781step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2454 node2454Labels := by rfl

def raw14782 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14782step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14782 raw14782Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw14782 raw14782Labels = mixedMoment B raw14782step0 raw14782step0Labels := by
      have ha : raw14782step0 = (fun i j => raw14782 (permutation566 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14782step0 raw14782; decide +kernel
      have hl : raw14782step0Labels = raw14782Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14782 raw14782Labels permutation566 permutation5
    mixedMoment B raw14782step0 raw14782step0Labels = mixedMoment B raw14782step1 raw14782step1Labels := by
      have ha : raw14782step1 = raw14782step0 := by apply Matrix.ext; unfold raw14782step1 raw14782step0; decide +kernel
      have hl : raw14782step0Labels = labelEmbedding1 ∘ raw14782step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14782step0 raw14782step0Labels raw14782step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw14783 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14783step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14783step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14783 raw14783Labels = mixedMoment B node2455 node2455Labels := by
  calc
    mixedMoment B raw14783 raw14783Labels = mixedMoment B raw14783step0 raw14783step0Labels := by
      have ha : raw14783step0 = (fun i j => raw14783 (permutation558 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14783step0 raw14783; decide +kernel
      have hl : raw14783step0Labels = raw14783Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14783 raw14783Labels permutation558 permutation5
    mixedMoment B raw14783step0 raw14783step0Labels = mixedMoment B raw14783step1 raw14783step1Labels := by
      have ha : raw14783step1 = raw14783step0 := by apply Matrix.ext; unfold raw14783step1 raw14783step0; decide +kernel
      have hl : raw14783step0Labels = labelEmbedding1 ∘ raw14783step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14783step0 raw14783step0Labels raw14783step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2455 node2455Labels := by rfl

def raw14784 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14784 raw14784Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw14784 raw14784Labels = mixedMoment B raw14784step0 raw14784step0Labels := by
      have hz : ∀ j, raw14784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14784step0 = (fun i j => raw14784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14784step0 raw14784; decide +kernel
      have hl : raw14784step0Labels = raw14784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14784 raw14784Labels permutation434 hz
    mixedMoment B raw14784step0 raw14784step0Labels = mixedMoment B raw14784step1 raw14784step1Labels := by
      have ha : raw14784step1 = (fun i j => raw14784step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14784step1 raw14784step0; decide +kernel
      have hl : raw14784step1Labels = raw14784step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14784step0 raw14784step0Labels permutation115 permutation5
    mixedMoment B raw14784step1 raw14784step1Labels = mixedMoment B raw14784step2 raw14784step2Labels := by
      have ha : raw14784step2 = raw14784step1 := by apply Matrix.ext; unfold raw14784step2 raw14784step1; decide +kernel
      have hl : raw14784step1Labels = labelEmbedding1 ∘ raw14784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14784step1 raw14784step1Labels raw14784step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw14785 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw14785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw14785step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14785step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw14785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14785 raw14785Labels = mixedMoment B node2463 node2463Labels := by
  calc
    mixedMoment B raw14785 raw14785Labels = mixedMoment B raw14785step0 raw14785step0Labels := by
      have ha : raw14785step0 = (fun i j => raw14785 (permutation557 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14785step0 raw14785; decide +kernel
      have hl : raw14785step0Labels = raw14785Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14785 raw14785Labels permutation557 permutation5
    mixedMoment B raw14785step0 raw14785step0Labels = mixedMoment B raw14785step1 raw14785step1Labels := by
      have ha : raw14785step1 = raw14785step0 := by apply Matrix.ext; unfold raw14785step1 raw14785step0; decide +kernel
      have hl : raw14785step0Labels = labelEmbedding1 ∘ raw14785step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14785step0 raw14785step0Labels raw14785step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2463 node2463Labels := by rfl

def raw14786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14786step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14786step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14786step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14786 raw14786Labels = mixedMoment B node2934 node2934Labels := by
  calc
    mixedMoment B raw14786 raw14786Labels = mixedMoment B raw14786step0 raw14786step0Labels := by
      have ha : raw14786step0 = (fun i j => raw14786 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14786step0 raw14786; decide +kernel
      have hl : raw14786step0Labels = raw14786Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14786 raw14786Labels permutation180 permutation5
    mixedMoment B raw14786step0 raw14786step0Labels = mixedMoment B raw14786step1 raw14786step1Labels := by
      have ha : raw14786step1 = -raw14786step0 := by apply Matrix.ext; change ∀ i j, raw14786step1 i j = -(raw14786step0 i j); unfold raw14786step1 raw14786step0; decide +kernel
      have hl : raw14786step1Labels = raw14786step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14786step1 raw14786step1Labels = mixedMoment B raw14786step2 raw14786step2Labels := by
      have ha : raw14786step2 = raw14786step1 := by apply Matrix.ext; unfold raw14786step2 raw14786step1; decide +kernel
      have hl : raw14786step1Labels = labelEmbedding1 ∘ raw14786step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14786step1 raw14786step1Labels raw14786step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2934 node2934Labels := by rfl

def raw14787 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14787step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14787 raw14787Labels = mixedMoment B node3970 node3970Labels := by
  calc
    mixedMoment B raw14787 raw14787Labels = mixedMoment B raw14787step0 raw14787step0Labels := by
      have ha : raw14787step0 = (fun i j => raw14787 (permutation566 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14787step0 raw14787; decide +kernel
      have hl : raw14787step0Labels = raw14787Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14787 raw14787Labels permutation566 permutation5
    mixedMoment B raw14787step0 raw14787step0Labels = mixedMoment B raw14787step1 raw14787step1Labels := by
      have ha : raw14787step1 = raw14787step0 := by apply Matrix.ext; unfold raw14787step1 raw14787step0; decide +kernel
      have hl : raw14787step0Labels = labelEmbedding1 ∘ raw14787step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14787step0 raw14787step0Labels raw14787step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3970 node3970Labels := by rfl

def raw14788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14788step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14788step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14788 raw14788Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw14788 raw14788Labels = mixedMoment B raw14788step0 raw14788step0Labels := by
      have ha : raw14788step0 = (fun i j => raw14788 (permutation350 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14788step0 raw14788; decide +kernel
      have hl : raw14788step0Labels = raw14788Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14788 raw14788Labels permutation350 permutation5
    mixedMoment B raw14788step0 raw14788step0Labels = mixedMoment B raw14788step1 raw14788step1Labels := by
      have ha : raw14788step1 = -raw14788step0 := by apply Matrix.ext; change ∀ i j, raw14788step1 i j = -(raw14788step0 i j); unfold raw14788step1 raw14788step0; decide +kernel
      have hl : raw14788step1Labels = raw14788step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14788step1 raw14788step1Labels = mixedMoment B raw14788step2 raw14788step2Labels := by
      have ha : raw14788step2 = raw14788step1 := by apply Matrix.ext; unfold raw14788step2 raw14788step1; decide +kernel
      have hl : raw14788step1Labels = labelEmbedding1 ∘ raw14788step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14788step1 raw14788step1Labels raw14788step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3724 node3724Labels := by rfl

def raw14789 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14789step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14789step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14789 raw14789Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw14789 raw14789Labels = mixedMoment B raw14789step0 raw14789step0Labels := by
      have hz : ∀ j, raw14789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14789step0 = (fun i j => raw14789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14789step0 raw14789; decide +kernel
      have hl : raw14789step0Labels = raw14789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14789 raw14789Labels permutation434 hz
    mixedMoment B raw14789step0 raw14789step0Labels = mixedMoment B raw14789step1 raw14789step1Labels := by
      have ha : raw14789step1 = (fun i j => raw14789step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14789step1 raw14789step0; decide +kernel
      have hl : raw14789step1Labels = raw14789step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14789step0 raw14789step0Labels permutation125 permutation5
    mixedMoment B raw14789step1 raw14789step1Labels = mixedMoment B raw14789step2 raw14789step2Labels := by
      have ha : raw14789step2 = raw14789step1 := by apply Matrix.ext; unfold raw14789step2 raw14789step1; decide +kernel
      have hl : raw14789step1Labels = labelEmbedding1 ∘ raw14789step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14789step1 raw14789step1Labels raw14789step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw14790 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw14790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14790step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14790step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14790 raw14790Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw14790 raw14790Labels = mixedMoment B raw14790step0 raw14790step0Labels := by
      have ha : raw14790step0 = (fun i j => raw14790 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14790step0 raw14790; decide +kernel
      have hl : raw14790step0Labels = raw14790Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14790 raw14790Labels permutation682 permutation7
    mixedMoment B raw14790step0 raw14790step0Labels = mixedMoment B raw14790step1 raw14790step1Labels := by
      have ha : raw14790step1 = -raw14790step0 := by apply Matrix.ext; change ∀ i j, raw14790step1 i j = -(raw14790step0 i j); unfold raw14790step1 raw14790step0; decide +kernel
      have hl : raw14790step1Labels = raw14790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14790step1 raw14790step1Labels = mixedMoment B raw14790step2 raw14790step2Labels := by
      have ha : raw14790step2 = raw14790step1 := by apply Matrix.ext; unfold raw14790step2 raw14790step1; decide +kernel
      have hl : raw14790step1Labels = labelEmbedding1 ∘ raw14790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14790step1 raw14790step1Labels raw14790step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw14791 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14791 raw14791Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw14791 raw14791Labels = mixedMoment B raw14791step0 raw14791step0Labels := by
      have ha : raw14791step0 = (fun i j => raw14791 (permutation180 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14791step0 raw14791; decide +kernel
      have hl : raw14791step0Labels = raw14791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14791 raw14791Labels permutation180 permutation4
    mixedMoment B raw14791step0 raw14791step0Labels = mixedMoment B raw14791step1 raw14791step1Labels := by
      have ha : raw14791step1 = -raw14791step0 := by apply Matrix.ext; change ∀ i j, raw14791step1 i j = -(raw14791step0 i j); unfold raw14791step1 raw14791step0; decide +kernel
      have hl : raw14791step1Labels = raw14791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw14792 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14792 raw14792Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw14792 raw14792Labels = mixedMoment B raw14792step0 raw14792step0Labels := by
      have ha : raw14792step0 = (fun i j => raw14792 (permutation634 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14792step0 raw14792; decide +kernel
      have hl : raw14792step0Labels = raw14792Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14792 raw14792Labels permutation634 permutation2
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw14793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14793 raw14793Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw14793 raw14793Labels = mixedMoment B raw14793step0 raw14793step0Labels := by
      have ha : raw14793step0 = (fun i j => raw14793 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14793step0 raw14793; decide +kernel
      have hl : raw14793step0Labels = raw14793Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14793 raw14793Labels permutation646 permutation2
    _ = mixedMoment B node3730 node3730Labels := by rfl

def raw14794 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14794 raw14794Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw14794 raw14794Labels = mixedMoment B raw14794step0 raw14794step0Labels := by
      have hz : ∀ j, raw14794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14794step0 = (fun i j => raw14794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14794step0 raw14794; decide +kernel
      have hl : raw14794step0Labels = raw14794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14794 raw14794Labels permutation434 hz
    mixedMoment B raw14794step0 raw14794step0Labels = mixedMoment B raw14794step1 raw14794step1Labels := by
      have ha : raw14794step1 = (fun i j => raw14794step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14794step1 raw14794step0; decide +kernel
      have hl : raw14794step1Labels = raw14794step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14794step0 raw14794step0Labels permutation145 permutation2
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw14795 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14795 raw14795Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw14795 raw14795Labels = mixedMoment B raw14795step0 raw14795step0Labels := by
      have ha : raw14795step0 = (fun i j => raw14795 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14795step0 raw14795; decide +kernel
      have hl : raw14795step0Labels = raw14795Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14795 raw14795Labels permutation646 permutation2
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw14796 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14796 raw14796Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw14796 raw14796Labels = mixedMoment B raw14796step0 raw14796step0Labels := by
      have ha : raw14796step0 = (fun i j => raw14796 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14796step0 raw14796; decide +kernel
      have hl : raw14796step0Labels = raw14796Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14796 raw14796Labels permutation646 permutation2
    _ = mixedMoment B node2587 node2587Labels := by rfl

def raw14797 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2]]
def raw14797Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14797step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![0, 0], ![-1, 1], ![-2, 2]]
def raw14797step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14797step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-2, 2]]
def raw14797step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14797step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw14797step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14797 raw14797Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw14797 raw14797Labels = mixedMoment B raw14797step0 raw14797step0Labels := by
      have hz : ∀ j, raw14797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14797step0 = (fun i j => raw14797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14797step0 raw14797; decide +kernel
      have hl : raw14797step0Labels = raw14797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14797 raw14797Labels permutation434 hz
    mixedMoment B raw14797step0 raw14797step0Labels = mixedMoment B raw14797step1 raw14797step1Labels := by
      have hz : ∀ j, raw14797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14797step1 = (fun i j => raw14797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14797step1 raw14797step0; decide +kernel
      have hl : raw14797step1Labels = raw14797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14797step0 raw14797step0Labels permutation80 hz
    mixedMoment B raw14797step1 raw14797step1Labels = mixedMoment B raw14797step2 raw14797step2Labels := by
      have ha : raw14797step2 = (fun i j => raw14797step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14797step2 raw14797step1; decide +kernel
      have hl : raw14797step2Labels = raw14797step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14797step1 raw14797step1Labels permutation31 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw14798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14798 raw14798Labels = mixedMoment B node2577 node2577Labels := by
  calc
    mixedMoment B raw14798 raw14798Labels = mixedMoment B raw14798step0 raw14798step0Labels := by
      have ha : raw14798step0 = (fun i j => raw14798 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14798step0 raw14798; decide +kernel
      have hl : raw14798step0Labels = raw14798Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14798 raw14798Labels permutation194 permutation4
    mixedMoment B raw14798step0 raw14798step0Labels = mixedMoment B raw14798step1 raw14798step1Labels := by
      have ha : raw14798step1 = -raw14798step0 := by apply Matrix.ext; change ∀ i j, raw14798step1 i j = -(raw14798step0 i j); unfold raw14798step1 raw14798step0; decide +kernel
      have hl : raw14798step1Labels = raw14798step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2577 node2577Labels := by rfl

def raw14799 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14799step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14799 raw14799Labels = mixedMoment B node3729 node3729Labels := by
  calc
    mixedMoment B raw14799 raw14799Labels = mixedMoment B raw14799step0 raw14799step0Labels := by
      have ha : raw14799step0 = (fun i j => raw14799 (permutation628 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14799step0 raw14799; decide +kernel
      have hl : raw14799step0Labels = raw14799Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14799 raw14799Labels permutation628 permutation2
    _ = mixedMoment B node3729 node3729Labels := by rfl

def raw14800 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14800 raw14800Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw14800 raw14800Labels = mixedMoment B raw14800step0 raw14800step0Labels := by
      have hz : ∀ j, raw14800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14800step0 = (fun i j => raw14800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14800step0 raw14800; decide +kernel
      have hl : raw14800step0Labels = raw14800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14800 raw14800Labels permutation434 hz
    mixedMoment B raw14800step0 raw14800step0Labels = mixedMoment B raw14800step1 raw14800step1Labels := by
      have ha : raw14800step1 = (fun i j => raw14800step0 (permutation141 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14800step1 raw14800step0; decide +kernel
      have hl : raw14800step1Labels = raw14800step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14800step0 raw14800step0Labels permutation141 permutation2
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw14801 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14801 raw14801Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw14801 raw14801Labels = mixedMoment B raw14801step0 raw14801step0Labels := by
      have ha : raw14801step0 = (fun i j => raw14801 (permutation642 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14801step0 raw14801; decide +kernel
      have hl : raw14801step0Labels = raw14801Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14801 raw14801Labels permutation642 permutation2
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw14802 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14802 raw14802Labels = mixedMoment B node2577 node2577Labels := by
  calc
    mixedMoment B raw14802 raw14802Labels = mixedMoment B raw14802step0 raw14802step0Labels := by
      have ha : raw14802step0 = (fun i j => raw14802 (permutation628 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14802step0 raw14802; decide +kernel
      have hl : raw14802step0Labels = raw14802Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14802 raw14802Labels permutation628 permutation2
    _ = mixedMoment B node2577 node2577Labels := by rfl

def raw14803 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14803 raw14803Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw14803 raw14803Labels = mixedMoment B raw14803step0 raw14803step0Labels := by
      have hz : ∀ j, raw14803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14803step0 = (fun i j => raw14803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14803step0 raw14803; decide +kernel
      have hl : raw14803step0Labels = raw14803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14803 raw14803Labels permutation346 hz
    mixedMoment B raw14803step0 raw14803step0Labels = mixedMoment B raw14803step1 raw14803step1Labels := by
      have ha : raw14803step1 = (fun i j => raw14803step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14803step1 raw14803step0; decide +kernel
      have hl : raw14803step1Labels = raw14803step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14803step0 raw14803step0Labels permutation36 permutation4
    mixedMoment B raw14803step1 raw14803step1Labels = mixedMoment B raw14803step2 raw14803step2Labels := by
      have ha : raw14803step2 = -raw14803step1 := by apply Matrix.ext; change ∀ i j, raw14803step2 i j = -(raw14803step1 i j); unfold raw14803step2 raw14803step1; decide +kernel
      have hl : raw14803step2Labels = raw14803step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw14804 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14804 raw14804Labels = mixedMoment B node3780 node3780Labels := by
  calc
    mixedMoment B raw14804 raw14804Labels = mixedMoment B raw14804step0 raw14804step0Labels := by
      have ha : raw14804step0 = (fun i j => raw14804 (permutation156 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14804step0 raw14804; decide +kernel
      have hl : raw14804step0Labels = raw14804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14804 raw14804Labels permutation156 permutation4
    mixedMoment B raw14804step0 raw14804step0Labels = mixedMoment B raw14804step1 raw14804step1Labels := by
      have ha : raw14804step1 = -raw14804step0 := by apply Matrix.ext; change ∀ i j, raw14804step1 i j = -(raw14804step0 i j); unfold raw14804step1 raw14804step0; decide +kernel
      have hl : raw14804step1Labels = raw14804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3780 node3780Labels := by rfl

def raw14805 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14805 raw14805Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw14805 raw14805Labels = mixedMoment B raw14805step0 raw14805step0Labels := by
      have ha : raw14805step0 = (fun i j => raw14805 (permutation568 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14805step0 raw14805; decide +kernel
      have hl : raw14805step0Labels = raw14805Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14805 raw14805Labels permutation568 permutation4
    _ = mixedMoment B node2974 node2974Labels := by rfl

def raw14806 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw14806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14806 raw14806Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw14806 raw14806Labels = mixedMoment B raw14806step0 raw14806step0Labels := by
      have ha : raw14806step0 = (fun i j => raw14806 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14806step0 raw14806; decide +kernel
      have hl : raw14806step0Labels = raw14806Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14806 raw14806Labels permutation153 permutation4
    mixedMoment B raw14806step0 raw14806step0Labels = mixedMoment B raw14806step1 raw14806step1Labels := by
      have ha : raw14806step1 = -raw14806step0 := by apply Matrix.ext; change ∀ i j, raw14806step1 i j = -(raw14806step0 i j); unfold raw14806step1 raw14806step0; decide +kernel
      have hl : raw14806step1Labels = raw14806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3781 node3781Labels := by rfl

def raw14807 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14807 raw14807Labels = mixedMoment B node3717 node3717Labels := by
  calc
    mixedMoment B raw14807 raw14807Labels = mixedMoment B raw14807step0 raw14807step0Labels := by
      have ha : raw14807step0 = (fun i j => raw14807 (permutation180 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14807step0 raw14807; decide +kernel
      have hl : raw14807step0Labels = raw14807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14807 raw14807Labels permutation180 permutation4
    mixedMoment B raw14807step0 raw14807step0Labels = mixedMoment B raw14807step1 raw14807step1Labels := by
      have ha : raw14807step1 = -raw14807step0 := by apply Matrix.ext; change ∀ i j, raw14807step1 i j = -(raw14807step0 i j); unfold raw14807step1 raw14807step0; decide +kernel
      have hl : raw14807step1Labels = raw14807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3717 node3717Labels := by rfl

def raw14808 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14808 raw14808Labels = mixedMoment B node2971 node2971Labels := by
  calc
    mixedMoment B raw14808 raw14808Labels = mixedMoment B raw14808step0 raw14808step0Labels := by
      have ha : raw14808step0 = (fun i j => raw14808 (permutation566 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14808step0 raw14808; decide +kernel
      have hl : raw14808step0Labels = raw14808Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14808 raw14808Labels permutation566 permutation4
    _ = mixedMoment B node2971 node2971Labels := by rfl

def raw14809 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw14809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14809 raw14809Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw14809 raw14809Labels = mixedMoment B raw14809step0 raw14809step0Labels := by
      have ha : raw14809step0 = (fun i j => raw14809 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14809step0 raw14809; decide +kernel
      have hl : raw14809step0Labels = raw14809Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14809 raw14809Labels permutation177 permutation4
    mixedMoment B raw14809step0 raw14809step0Labels = mixedMoment B raw14809step1 raw14809step1Labels := by
      have ha : raw14809step1 = -raw14809step0 := by apply Matrix.ext; change ∀ i j, raw14809step1 i j = -(raw14809step0 i j); unfold raw14809step1 raw14809step0; decide +kernel
      have hl : raw14809step1Labels = raw14809step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3720 node3720Labels := by rfl

def raw14810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14810step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14810step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14810 raw14810Labels = mixedMoment B node2549 node2549Labels := by
  calc
    mixedMoment B raw14810 raw14810Labels = mixedMoment B raw14810step0 raw14810step0Labels := by
      have ha : raw14810step0 = (fun i j => raw14810 (permutation180 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14810step0 raw14810; decide +kernel
      have hl : raw14810step0Labels = raw14810Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14810 raw14810Labels permutation180 permutation4
    mixedMoment B raw14810step0 raw14810step0Labels = mixedMoment B raw14810step1 raw14810step1Labels := by
      have ha : raw14810step1 = -raw14810step0 := by apply Matrix.ext; change ∀ i j, raw14810step1 i j = -(raw14810step0 i j); unfold raw14810step1 raw14810step0; decide +kernel
      have hl : raw14810step1Labels = raw14810step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2549 node2549Labels := by rfl

def raw14811 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14811 raw14811Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw14811 raw14811Labels = mixedMoment B raw14811step0 raw14811step0Labels := by
      have ha : raw14811step0 = (fun i j => raw14811 (permutation641 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14811step0 raw14811; decide +kernel
      have hl : raw14811step0Labels = raw14811Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14811 raw14811Labels permutation641 permutation2
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw14812 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14812 raw14812Labels = mixedMoment B node2578 node2578Labels := by
  calc
    mixedMoment B raw14812 raw14812Labels = mixedMoment B raw14812step0 raw14812step0Labels := by
      have ha : raw14812step0 = (fun i j => raw14812 (permutation627 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14812step0 raw14812; decide +kernel
      have hl : raw14812step0Labels = raw14812Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14812 raw14812Labels permutation627 permutation2
    _ = mixedMoment B node2578 node2578Labels := by rfl

def raw14813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14813step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14813step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14813step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14813step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14813 raw14813Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw14813 raw14813Labels = mixedMoment B raw14813step0 raw14813step0Labels := by
      have ha : raw14813step0 = (fun i j => raw14813 (permutation461 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14813step0 raw14813; decide +kernel
      have hl : raw14813step0Labels = raw14813Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14813 raw14813Labels permutation461 permutation4
    mixedMoment B raw14813step0 raw14813step0Labels = mixedMoment B raw14813step1 raw14813step1Labels := by
      have ha : raw14813step1 = -raw14813step0 := by apply Matrix.ext; change ∀ i j, raw14813step1 i j = -(raw14813step0 i j); unfold raw14813step1 raw14813step0; decide +kernel
      have hl : raw14813step1Labels = raw14813step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14813step1 raw14813step1Labels = mixedMoment B raw14813step2 raw14813step2Labels := by
      have ha : raw14813step2 = raw14813step1 := by apply Matrix.ext; unfold raw14813step2 raw14813step1; decide +kernel
      have hl : raw14813step1Labels = labelEmbedding7 ∘ raw14813step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14813step1 raw14813step1Labels raw14813step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw14814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14814step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14814step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14814step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14814step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14814 raw14814Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw14814 raw14814Labels = mixedMoment B raw14814step0 raw14814step0Labels := by
      have ha : raw14814step0 = (fun i j => raw14814 (permutation461 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14814step0 raw14814; decide +kernel
      have hl : raw14814step0Labels = raw14814Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14814 raw14814Labels permutation461 permutation4
    mixedMoment B raw14814step0 raw14814step0Labels = mixedMoment B raw14814step1 raw14814step1Labels := by
      have ha : raw14814step1 = -raw14814step0 := by apply Matrix.ext; change ∀ i j, raw14814step1 i j = -(raw14814step0 i j); unfold raw14814step1 raw14814step0; decide +kernel
      have hl : raw14814step1Labels = raw14814step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14814step1 raw14814step1Labels = mixedMoment B raw14814step2 raw14814step2Labels := by
      have ha : raw14814step2 = raw14814step1 := by apply Matrix.ext; unfold raw14814step2 raw14814step1; decide +kernel
      have hl : raw14814step1Labels = labelEmbedding7 ∘ raw14814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14814step1 raw14814step1Labels raw14814step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw14815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14815step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14815step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14815step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14815 raw14815Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw14815 raw14815Labels = mixedMoment B raw14815step0 raw14815step0Labels := by
      have ha : raw14815step0 = (fun i j => raw14815 (permutation461 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14815step0 raw14815; decide +kernel
      have hl : raw14815step0Labels = raw14815Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14815 raw14815Labels permutation461 permutation4
    mixedMoment B raw14815step0 raw14815step0Labels = mixedMoment B raw14815step1 raw14815step1Labels := by
      have ha : raw14815step1 = -raw14815step0 := by apply Matrix.ext; change ∀ i j, raw14815step1 i j = -(raw14815step0 i j); unfold raw14815step1 raw14815step0; decide +kernel
      have hl : raw14815step1Labels = raw14815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14815step1 raw14815step1Labels = mixedMoment B raw14815step2 raw14815step2Labels := by
      have ha : raw14815step2 = raw14815step1 := by apply Matrix.ext; unfold raw14815step2 raw14815step1; decide +kernel
      have hl : raw14815step1Labels = labelEmbedding7 ∘ raw14815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14815step1 raw14815step1Labels raw14815step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw14816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14816step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14816step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14816step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14816step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14816 raw14816Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw14816 raw14816Labels = mixedMoment B raw14816step0 raw14816step0Labels := by
      have ha : raw14816step0 = (fun i j => raw14816 (permutation491 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14816step0 raw14816; decide +kernel
      have hl : raw14816step0Labels = raw14816Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14816 raw14816Labels permutation491 permutation4
    mixedMoment B raw14816step0 raw14816step0Labels = mixedMoment B raw14816step1 raw14816step1Labels := by
      have ha : raw14816step1 = -raw14816step0 := by apply Matrix.ext; change ∀ i j, raw14816step1 i j = -(raw14816step0 i j); unfold raw14816step1 raw14816step0; decide +kernel
      have hl : raw14816step1Labels = raw14816step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14816step1 raw14816step1Labels = mixedMoment B raw14816step2 raw14816step2Labels := by
      have ha : raw14816step2 = raw14816step1 := by apply Matrix.ext; unfold raw14816step2 raw14816step1; decide +kernel
      have hl : raw14816step1Labels = labelEmbedding7 ∘ raw14816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14816step1 raw14816step1Labels raw14816step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw14817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14817step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14817 raw14817Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw14817 raw14817Labels = mixedMoment B raw14817step0 raw14817step0Labels := by
      have ha : raw14817step0 = (fun i j => raw14817 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14817step0 raw14817; decide +kernel
      have hl : raw14817step0Labels = raw14817Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14817 raw14817Labels permutation494 permutation6
    mixedMoment B raw14817step0 raw14817step0Labels = mixedMoment B raw14817step1 raw14817step1Labels := by
      have ha : raw14817step1 = raw14817step0 := by apply Matrix.ext; unfold raw14817step1 raw14817step0; decide +kernel
      have hl : raw14817step0Labels = labelEmbedding9 ∘ raw14817step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14817step0 raw14817step0Labels raw14817step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw14818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14818 raw14818Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw14818 raw14818Labels = mixedMoment B raw14818step0 raw14818step0Labels := by
      have hz : ∀ j, raw14818 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14818step0 = (fun i j => raw14818 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14818step0 raw14818; decide +kernel
      have hl : raw14818step0Labels = raw14818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14818 raw14818Labels permutation265 hz
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw14819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14819step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14819step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14819step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14819step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14819 raw14819Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw14819 raw14819Labels = mixedMoment B raw14819step0 raw14819step0Labels := by
      have hz : ∀ j, raw14819 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14819step0 = (fun i j => raw14819 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14819step0 raw14819; decide +kernel
      have hl : raw14819step0Labels = raw14819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14819 raw14819Labels permutation265 hz
    mixedMoment B raw14819step0 raw14819step0Labels = mixedMoment B raw14819step1 raw14819step1Labels := by
      have ha : raw14819step1 = (fun i j => raw14819step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14819step1 raw14819step0; decide +kernel
      have hl : raw14819step1Labels = raw14819step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14819step0 raw14819step0Labels permutation92 permutation4
    mixedMoment B raw14819step1 raw14819step1Labels = mixedMoment B raw14819step2 raw14819step2Labels := by
      have ha : raw14819step2 = -raw14819step1 := by apply Matrix.ext; change ∀ i j, raw14819step2 i j = -(raw14819step1 i j); unfold raw14819step2 raw14819step1; decide +kernel
      have hl : raw14819step2Labels = raw14819step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14819step2 raw14819step2Labels = mixedMoment B raw14819step3 raw14819step3Labels := by
      have ha : raw14819step3 = raw14819step2 := by apply Matrix.ext; unfold raw14819step3 raw14819step2; decide +kernel
      have hl : raw14819step2Labels = labelEmbedding7 ∘ raw14819step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14819step2 raw14819step2Labels raw14819step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw14820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14820step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14820step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14820step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14820step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14820 raw14820Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw14820 raw14820Labels = mixedMoment B raw14820step0 raw14820step0Labels := by
      have hz : ∀ j, raw14820 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14820step0 = (fun i j => raw14820 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14820step0 raw14820; decide +kernel
      have hl : raw14820step0Labels = raw14820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14820 raw14820Labels permutation265 hz
    mixedMoment B raw14820step0 raw14820step0Labels = mixedMoment B raw14820step1 raw14820step1Labels := by
      have ha : raw14820step1 = (fun i j => raw14820step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14820step1 raw14820step0; decide +kernel
      have hl : raw14820step1Labels = raw14820step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14820step0 raw14820step0Labels permutation92 permutation4
    mixedMoment B raw14820step1 raw14820step1Labels = mixedMoment B raw14820step2 raw14820step2Labels := by
      have ha : raw14820step2 = -raw14820step1 := by apply Matrix.ext; change ∀ i j, raw14820step2 i j = -(raw14820step1 i j); unfold raw14820step2 raw14820step1; decide +kernel
      have hl : raw14820step2Labels = raw14820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14820step2 raw14820step2Labels = mixedMoment B raw14820step3 raw14820step3Labels := by
      have ha : raw14820step3 = raw14820step2 := by apply Matrix.ext; unfold raw14820step3 raw14820step2; decide +kernel
      have hl : raw14820step2Labels = labelEmbedding7 ∘ raw14820step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14820step2 raw14820step2Labels raw14820step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw14821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14821 raw14821Labels = mixedMoment B node5154 node5154Labels := by
  calc
    mixedMoment B raw14821 raw14821Labels = mixedMoment B raw14821step0 raw14821step0Labels := by
      have ha : raw14821step0 = (fun i j => raw14821 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14821step0 raw14821; decide +kernel
      have hl : raw14821step0Labels = raw14821Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14821 raw14821Labels permutation158 permutation2
    _ = mixedMoment B node5154 node5154Labels := by rfl

def raw14822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14822step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14822 raw14822Labels = mixedMoment B node5342 node5342Labels := by
  calc
    mixedMoment B raw14822 raw14822Labels = mixedMoment B raw14822step0 raw14822step0Labels := by
      have ha : raw14822step0 = (fun i j => raw14822 (permutation642 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14822step0 raw14822; decide +kernel
      have hl : raw14822step0Labels = raw14822Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14822 raw14822Labels permutation642 permutation5
    mixedMoment B raw14822step0 raw14822step0Labels = mixedMoment B raw14822step1 raw14822step1Labels := by
      have ha : raw14822step1 = raw14822step0 := by apply Matrix.ext; unfold raw14822step1 raw14822step0; decide +kernel
      have hl : raw14822step0Labels = labelEmbedding8 ∘ raw14822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14822step0 raw14822step0Labels raw14822step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5342 node5342Labels := by rfl

def raw14823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14823step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14823step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14823step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14823step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14823 raw14823Labels = mixedMoment B node5131 node5131Labels := by
  calc
    mixedMoment B raw14823 raw14823Labels = mixedMoment B raw14823step0 raw14823step0Labels := by
      have ha : raw14823step0 = (fun i j => raw14823 (permutation460 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14823step0 raw14823; decide +kernel
      have hl : raw14823step0Labels = raw14823Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14823 raw14823Labels permutation460 permutation4
    mixedMoment B raw14823step0 raw14823step0Labels = mixedMoment B raw14823step1 raw14823step1Labels := by
      have ha : raw14823step1 = -raw14823step0 := by apply Matrix.ext; change ∀ i j, raw14823step1 i j = -(raw14823step0 i j); unfold raw14823step1 raw14823step0; decide +kernel
      have hl : raw14823step1Labels = raw14823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14823step1 raw14823step1Labels = mixedMoment B raw14823step2 raw14823step2Labels := by
      have ha : raw14823step2 = raw14823step1 := by apply Matrix.ext; unfold raw14823step2 raw14823step1; decide +kernel
      have hl : raw14823step1Labels = labelEmbedding7 ∘ raw14823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14823step1 raw14823step1Labels raw14823step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5131 node5131Labels := by rfl

def raw14824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14824step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14824 raw14824Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw14824 raw14824Labels = mixedMoment B raw14824step0 raw14824step0Labels := by
      have ha : raw14824step0 = (fun i j => raw14824 (permutation627 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14824step0 raw14824; decide +kernel
      have hl : raw14824step0Labels = raw14824Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14824 raw14824Labels permutation627 permutation5
    mixedMoment B raw14824step0 raw14824step0Labels = mixedMoment B raw14824step1 raw14824step1Labels := by
      have ha : raw14824step1 = raw14824step0 := by apply Matrix.ext; unfold raw14824step1 raw14824step0; decide +kernel
      have hl : raw14824step0Labels = labelEmbedding8 ∘ raw14824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14824step0 raw14824step0Labels raw14824step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw14825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14825step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14825 raw14825Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw14825 raw14825Labels = mixedMoment B raw14825step0 raw14825step0Labels := by
      have ha : raw14825step0 = (fun i j => raw14825 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14825step0 raw14825; decide +kernel
      have hl : raw14825step0Labels = raw14825Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14825 raw14825Labels permutation494 permutation6
    mixedMoment B raw14825step0 raw14825step0Labels = mixedMoment B raw14825step1 raw14825step1Labels := by
      have ha : raw14825step1 = raw14825step0 := by apply Matrix.ext; unfold raw14825step1 raw14825step0; decide +kernel
      have hl : raw14825step0Labels = labelEmbedding9 ∘ raw14825step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14825step0 raw14825step0Labels raw14825step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw14826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14826 raw14826Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw14826 raw14826Labels = mixedMoment B raw14826step0 raw14826step0Labels := by
      have ha : raw14826step0 = (fun i j => raw14826 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14826step0 raw14826; decide +kernel
      have hl : raw14826step0Labels = raw14826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14826 raw14826Labels permutation154 permutation2
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw14827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14827 raw14827Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw14827 raw14827Labels = mixedMoment B raw14827step0 raw14827step0Labels := by
      have ha : raw14827step0 = (fun i j => raw14827 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14827step0 raw14827; decide +kernel
      have hl : raw14827step0Labels = raw14827Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14827 raw14827Labels permutation178 permutation2
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw14828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14828 raw14828Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw14828 raw14828Labels = mixedMoment B raw14828step0 raw14828step0Labels := by
      have ha : raw14828step0 = (fun i j => raw14828 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14828step0 raw14828; decide +kernel
      have hl : raw14828step0Labels = raw14828Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14828 raw14828Labels permutation154 permutation2
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw14829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14829 raw14829Labels = mixedMoment B node5131 node5131Labels := by
  calc
    mixedMoment B raw14829 raw14829Labels = mixedMoment B raw14829step0 raw14829step0Labels := by
      have ha : raw14829step0 = (fun i j => raw14829 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14829step0 raw14829; decide +kernel
      have hl : raw14829step0Labels = raw14829Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14829 raw14829Labels permutation153 permutation2
    _ = mixedMoment B node5131 node5131Labels := by rfl

def raw14830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw14830step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14830step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14830step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14830step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14830 raw14830Labels = mixedMoment B node5342 node5342Labels := by
  calc
    mixedMoment B raw14830 raw14830Labels = mixedMoment B raw14830step0 raw14830step0Labels := by
      have ha : raw14830step0 = (fun i j => raw14830 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14830step0 raw14830; decide +kernel
      have hl : raw14830step0Labels = raw14830Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14830 raw14830Labels permutation681 permutation3
    mixedMoment B raw14830step0 raw14830step0Labels = mixedMoment B raw14830step1 raw14830step1Labels := by
      have ha : raw14830step1 = -raw14830step0 := by apply Matrix.ext; change ∀ i j, raw14830step1 i j = -(raw14830step0 i j); unfold raw14830step1 raw14830step0; decide +kernel
      have hl : raw14830step1Labels = raw14830step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14830step1 raw14830step1Labels = mixedMoment B raw14830step2 raw14830step2Labels := by
      have ha : raw14830step2 = raw14830step1 := by apply Matrix.ext; unfold raw14830step2 raw14830step1; decide +kernel
      have hl : raw14830step1Labels = labelEmbedding6 ∘ raw14830step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14830step1 raw14830step1Labels raw14830step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5342 node5342Labels := by rfl

def raw14831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14831step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14831step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14831step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14831step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14831step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14831 raw14831Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw14831 raw14831Labels = mixedMoment B raw14831step0 raw14831step0Labels := by
      have ha : raw14831step0 = (fun i j => raw14831 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14831step0 raw14831; decide +kernel
      have hl : raw14831step0Labels = raw14831Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14831 raw14831Labels permutation688 permutation3
    mixedMoment B raw14831step0 raw14831step0Labels = mixedMoment B raw14831step1 raw14831step1Labels := by
      have ha : raw14831step1 = -raw14831step0 := by apply Matrix.ext; change ∀ i j, raw14831step1 i j = -(raw14831step0 i j); unfold raw14831step1 raw14831step0; decide +kernel
      have hl : raw14831step1Labels = raw14831step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14831step1 raw14831step1Labels = mixedMoment B raw14831step2 raw14831step2Labels := by
      have ha : raw14831step2 = raw14831step1 := by apply Matrix.ext; unfold raw14831step2 raw14831step1; decide +kernel
      have hl : raw14831step1Labels = labelEmbedding6 ∘ raw14831step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14831step1 raw14831step1Labels raw14831step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw14832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14832step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14832step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14832step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14832step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14832 raw14832Labels = mixedMoment B node5154 node5154Labels := by
  calc
    mixedMoment B raw14832 raw14832Labels = mixedMoment B raw14832step0 raw14832step0Labels := by
      have ha : raw14832step0 = (fun i j => raw14832 (permutation453 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14832step0 raw14832; decide +kernel
      have hl : raw14832step0Labels = raw14832Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14832 raw14832Labels permutation453 permutation4
    mixedMoment B raw14832step0 raw14832step0Labels = mixedMoment B raw14832step1 raw14832step1Labels := by
      have ha : raw14832step1 = -raw14832step0 := by apply Matrix.ext; change ∀ i j, raw14832step1 i j = -(raw14832step0 i j); unfold raw14832step1 raw14832step0; decide +kernel
      have hl : raw14832step1Labels = raw14832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14832step1 raw14832step1Labels = mixedMoment B raw14832step2 raw14832step2Labels := by
      have ha : raw14832step2 = raw14832step1 := by apply Matrix.ext; unfold raw14832step2 raw14832step1; decide +kernel
      have hl : raw14832step1Labels = labelEmbedding7 ∘ raw14832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14832step1 raw14832step1Labels raw14832step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5154 node5154Labels := by rfl

def raw14833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14833step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14833step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14833step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14833 raw14833Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw14833 raw14833Labels = mixedMoment B raw14833step0 raw14833step0Labels := by
      have ha : raw14833step0 = (fun i j => raw14833 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14833step0 raw14833; decide +kernel
      have hl : raw14833step0Labels = raw14833Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14833 raw14833Labels permutation181 permutation7
    mixedMoment B raw14833step0 raw14833step0Labels = mixedMoment B raw14833step1 raw14833step1Labels := by
      have ha : raw14833step1 = -raw14833step0 := by apply Matrix.ext; change ∀ i j, raw14833step1 i j = -(raw14833step0 i j); unfold raw14833step1 raw14833step0; decide +kernel
      have hl : raw14833step1Labels = raw14833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14833step1 raw14833step1Labels = mixedMoment B raw14833step2 raw14833step2Labels := by
      have ha : raw14833step2 = raw14833step1 := by apply Matrix.ext; unfold raw14833step2 raw14833step1; decide +kernel
      have hl : raw14833step1Labels = labelEmbedding10 ∘ raw14833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14833step1 raw14833step1Labels raw14833step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw14834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw14834step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14834step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw14834step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14834step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw14834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14834 raw14834Labels = mixedMoment B node4783 node4783Labels := by
  calc
    mixedMoment B raw14834 raw14834Labels = mixedMoment B raw14834step0 raw14834step0Labels := by
      have ha : raw14834step0 = (fun i j => raw14834 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14834step0 raw14834; decide +kernel
      have hl : raw14834step0Labels = raw14834Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14834 raw14834Labels permutation682 permutation3
    mixedMoment B raw14834step0 raw14834step0Labels = mixedMoment B raw14834step1 raw14834step1Labels := by
      have ha : raw14834step1 = -raw14834step0 := by apply Matrix.ext; change ∀ i j, raw14834step1 i j = -(raw14834step0 i j); unfold raw14834step1 raw14834step0; decide +kernel
      have hl : raw14834step1Labels = raw14834step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14834step1 raw14834step1Labels = mixedMoment B raw14834step2 raw14834step2Labels := by
      have ha : raw14834step2 = raw14834step1 := by apply Matrix.ext; unfold raw14834step2 raw14834step1; decide +kernel
      have hl : raw14834step1Labels = labelEmbedding6 ∘ raw14834step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14834step1 raw14834step1Labels raw14834step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4783 node4783Labels := by rfl

def raw14835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw14835step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14835step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14835step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14835step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14835 raw14835Labels = mixedMoment B node4784 node4784Labels := by
  calc
    mixedMoment B raw14835 raw14835Labels = mixedMoment B raw14835step0 raw14835step0Labels := by
      have ha : raw14835step0 = (fun i j => raw14835 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14835step0 raw14835; decide +kernel
      have hl : raw14835step0Labels = raw14835Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14835 raw14835Labels permutation681 permutation3
    mixedMoment B raw14835step0 raw14835step0Labels = mixedMoment B raw14835step1 raw14835step1Labels := by
      have ha : raw14835step1 = -raw14835step0 := by apply Matrix.ext; change ∀ i j, raw14835step1 i j = -(raw14835step0 i j); unfold raw14835step1 raw14835step0; decide +kernel
      have hl : raw14835step1Labels = raw14835step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14835step1 raw14835step1Labels = mixedMoment B raw14835step2 raw14835step2Labels := by
      have ha : raw14835step2 = raw14835step1 := by apply Matrix.ext; unfold raw14835step2 raw14835step1; decide +kernel
      have hl : raw14835step1Labels = labelEmbedding6 ∘ raw14835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14835step1 raw14835step1Labels raw14835step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4784 node4784Labels := by rfl

def raw14836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14836step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14836step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14836step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14836step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14836 raw14836Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw14836 raw14836Labels = mixedMoment B raw14836step0 raw14836step0Labels := by
      have ha : raw14836step0 = (fun i j => raw14836 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14836step0 raw14836; decide +kernel
      have hl : raw14836step0Labels = raw14836Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14836 raw14836Labels permutation688 permutation3
    mixedMoment B raw14836step0 raw14836step0Labels = mixedMoment B raw14836step1 raw14836step1Labels := by
      have ha : raw14836step1 = -raw14836step0 := by apply Matrix.ext; change ∀ i j, raw14836step1 i j = -(raw14836step0 i j); unfold raw14836step1 raw14836step0; decide +kernel
      have hl : raw14836step1Labels = raw14836step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14836step1 raw14836step1Labels = mixedMoment B raw14836step2 raw14836step2Labels := by
      have ha : raw14836step2 = raw14836step1 := by apply Matrix.ext; unfold raw14836step2 raw14836step1; decide +kernel
      have hl : raw14836step1Labels = labelEmbedding6 ∘ raw14836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14836step1 raw14836step1Labels raw14836step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw14837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw14837step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw14837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14837 raw14837Labels = mixedMoment B node4783 node4783Labels := by
  calc
    mixedMoment B raw14837 raw14837Labels = mixedMoment B raw14837step0 raw14837step0Labels := by
      have ha : raw14837step0 = (fun i j => raw14837 (permutation641 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14837step0 raw14837; decide +kernel
      have hl : raw14837step0Labels = raw14837Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14837 raw14837Labels permutation641 permutation5
    mixedMoment B raw14837step0 raw14837step0Labels = mixedMoment B raw14837step1 raw14837step1Labels := by
      have ha : raw14837step1 = raw14837step0 := by apply Matrix.ext; unfold raw14837step1 raw14837step0; decide +kernel
      have hl : raw14837step0Labels = labelEmbedding8 ∘ raw14837step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14837step0 raw14837step0Labels raw14837step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4783 node4783Labels := by rfl

def raw14838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw14838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14838step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14838 raw14838Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw14838 raw14838Labels = mixedMoment B raw14838step0 raw14838step0Labels := by
      have ha : raw14838step0 = (fun i j => raw14838 (permutation627 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14838step0 raw14838; decide +kernel
      have hl : raw14838step0Labels = raw14838Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14838 raw14838Labels permutation627 permutation5
    mixedMoment B raw14838step0 raw14838step0Labels = mixedMoment B raw14838step1 raw14838step1Labels := by
      have ha : raw14838step1 = raw14838step0 := by apply Matrix.ext; unfold raw14838step1 raw14838step0; decide +kernel
      have hl : raw14838step0Labels = labelEmbedding8 ∘ raw14838step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14838step0 raw14838step0Labels raw14838step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw14839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14839 raw14839Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw14839 raw14839Labels = mixedMoment B raw14839step0 raw14839step0Labels := by
      have ha : raw14839step0 = (fun i j => raw14839 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14839step0 raw14839; decide +kernel
      have hl : raw14839step0Labels = raw14839Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14839 raw14839Labels permutation494 permutation6
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw14840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14840 raw14840Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw14840 raw14840Labels = mixedMoment B raw14840step0 raw14840step0Labels := by
      have ha : raw14840step0 = (fun i j => raw14840 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14840step0 raw14840; decide +kernel
      have hl : raw14840step0Labels = raw14840Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14840 raw14840Labels permutation494 permutation6
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw14841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14841 raw14841Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw14841 raw14841Labels = mixedMoment B raw14841step0 raw14841step0Labels := by
      have ha : raw14841step0 = (fun i j => raw14841 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14841step0 raw14841; decide +kernel
      have hl : raw14841step0Labels = raw14841Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14841 raw14841Labels permutation494 permutation6
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw14842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14842 raw14842Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw14842 raw14842Labels = mixedMoment B raw14842step0 raw14842step0Labels := by
      have ha : raw14842step0 = (fun i j => raw14842 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14842step0 raw14842; decide +kernel
      have hl : raw14842step0Labels = raw14842Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14842 raw14842Labels permutation494 permutation6
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw14843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14843 raw14843Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw14843 raw14843Labels = mixedMoment B raw14843step0 raw14843step0Labels := by
      have ha : raw14843step0 = (fun i j => raw14843 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14843step0 raw14843; decide +kernel
      have hl : raw14843step0Labels = raw14843Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14843 raw14843Labels permutation494 permutation6
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw14844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14844 raw14844Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw14844 raw14844Labels = mixedMoment B raw14844step0 raw14844step0Labels := by
      have hz : ∀ j, raw14844 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14844step0 = (fun i j => raw14844 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14844step0 raw14844; decide +kernel
      have hl : raw14844step0Labels = raw14844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14844 raw14844Labels permutation265 hz
    mixedMoment B raw14844step0 raw14844step0Labels = mixedMoment B raw14844step1 raw14844step1Labels := by
      have ha : raw14844step1 = (fun i j => raw14844step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14844step1 raw14844step0; decide +kernel
      have hl : raw14844step1Labels = raw14844step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14844step0 raw14844step0Labels permutation38 permutation3
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw14845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw14845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14845 raw14845Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw14845 raw14845Labels = mixedMoment B raw14845step0 raw14845step0Labels := by
      have hz : ∀ j, raw14845 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14845step0 = (fun i j => raw14845 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14845step0 raw14845; decide +kernel
      have hl : raw14845step0Labels = raw14845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14845 raw14845Labels permutation265 hz
    mixedMoment B raw14845step0 raw14845step0Labels = mixedMoment B raw14845step1 raw14845step1Labels := by
      have ha : raw14845step1 = (fun i j => raw14845step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14845step1 raw14845step0; decide +kernel
      have hl : raw14845step1Labels = raw14845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14845step0 raw14845step0Labels permutation151 permutation3
    mixedMoment B raw14845step1 raw14845step1Labels = mixedMoment B raw14845step2 raw14845step2Labels := by
      have ha : raw14845step2 = -raw14845step1 := by apply Matrix.ext; change ∀ i j, raw14845step2 i j = -(raw14845step1 i j); unfold raw14845step2 raw14845step1; decide +kernel
      have hl : raw14845step2Labels = raw14845step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw14846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14846step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14846 raw14846Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw14846 raw14846Labels = mixedMoment B raw14846step0 raw14846step0Labels := by
      have hz : ∀ j, raw14846 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14846step0 = (fun i j => raw14846 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14846step0 raw14846; decide +kernel
      have hl : raw14846step0Labels = raw14846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14846 raw14846Labels permutation265 hz
    mixedMoment B raw14846step0 raw14846step0Labels = mixedMoment B raw14846step1 raw14846step1Labels := by
      have ha : raw14846step1 = (fun i j => raw14846step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14846step1 raw14846step0; decide +kernel
      have hl : raw14846step1Labels = raw14846step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14846step0 raw14846step0Labels permutation97 permutation6
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw14847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14847step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14847 raw14847Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw14847 raw14847Labels = mixedMoment B raw14847step0 raw14847step0Labels := by
      have hz : ∀ j, raw14847 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14847step0 = (fun i j => raw14847 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14847step0 raw14847; decide +kernel
      have hl : raw14847step0Labels = raw14847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14847 raw14847Labels permutation265 hz
    mixedMoment B raw14847step0 raw14847step0Labels = mixedMoment B raw14847step1 raw14847step1Labels := by
      have ha : raw14847step1 = (fun i j => raw14847step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14847step1 raw14847step0; decide +kernel
      have hl : raw14847step1Labels = raw14847step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14847step0 raw14847step0Labels permutation97 permutation6
    _ = mixedMoment B node3814 node3814Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
