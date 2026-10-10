import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11776step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11776 raw11776Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw11776 raw11776Labels = mixedMoment B raw11776step0 raw11776step0Labels := by
      have ha : raw11776step0 = (fun i j => raw11776 (permutation427 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11776step0 raw11776; decide +kernel
      have hl : raw11776step0Labels = raw11776Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11776 raw11776Labels permutation427 permutation6
    mixedMoment B raw11776step0 raw11776step0Labels = mixedMoment B raw11776step1 raw11776step1Labels := by
      have ha : raw11776step1 = raw11776step0 := by apply Matrix.ext; unfold raw11776step1 raw11776step0; decide +kernel
      have hl : raw11776step0Labels = labelEmbedding9 ∘ raw11776step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11776step0 raw11776step0Labels raw11776step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw11777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11777step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11777step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11777 raw11777Labels = mixedMoment B node4566 node4566Labels := by
  calc
    mixedMoment B raw11777 raw11777Labels = mixedMoment B raw11777step0 raw11777step0Labels := by
      have ha : raw11777step0 = (fun i j => raw11777 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11777step0 raw11777; decide +kernel
      have hl : raw11777step0Labels = raw11777Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11777 raw11777Labels permutation197 permutation3
    mixedMoment B raw11777step0 raw11777step0Labels = mixedMoment B raw11777step1 raw11777step1Labels := by
      have ha : raw11777step1 = raw11777step0 := by apply Matrix.ext; unfold raw11777step1 raw11777step0; decide +kernel
      have hl : raw11777step0Labels = labelEmbedding6 ∘ raw11777step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11777step0 raw11777step0Labels raw11777step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4566 node4566Labels := by rfl

def raw11778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw11778step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11778step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11778step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11778step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11778 raw11778Labels = mixedMoment B node5208 node5208Labels := by
  calc
    mixedMoment B raw11778 raw11778Labels = mixedMoment B raw11778step0 raw11778step0Labels := by
      have ha : raw11778step0 = (fun i j => raw11778 (permutation364 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11778step0 raw11778; decide +kernel
      have hl : raw11778step0Labels = raw11778Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11778 raw11778Labels permutation364 permutation4
    mixedMoment B raw11778step0 raw11778step0Labels = mixedMoment B raw11778step1 raw11778step1Labels := by
      have ha : raw11778step1 = -raw11778step0 := by apply Matrix.ext; change ∀ i j, raw11778step1 i j = -(raw11778step0 i j); unfold raw11778step1 raw11778step0; decide +kernel
      have hl : raw11778step1Labels = raw11778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11778step1 raw11778step1Labels = mixedMoment B raw11778step2 raw11778step2Labels := by
      have ha : raw11778step2 = raw11778step1 := by apply Matrix.ext; unfold raw11778step2 raw11778step1; decide +kernel
      have hl : raw11778step1Labels = labelEmbedding7 ∘ raw11778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11778step1 raw11778step1Labels raw11778step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5208 node5208Labels := by rfl

def raw11779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11779 raw11779Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw11779 raw11779Labels = mixedMoment B raw11779step0 raw11779step0Labels := by
      have hz : ∀ j, raw11779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11779step0 = (fun i j => raw11779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11779step0 raw11779; decide +kernel
      have hl : raw11779step0Labels = raw11779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11779 raw11779Labels permutation434 hz
    mixedMoment B raw11779step0 raw11779step0Labels = mixedMoment B raw11779step1 raw11779step1Labels := by
      have ha : raw11779step1 = (fun i j => raw11779step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11779step1 raw11779step0; decide +kernel
      have hl : raw11779step1Labels = raw11779step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11779step0 raw11779step0Labels permutation38 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw11780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11780 raw11780Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw11780 raw11780Labels = mixedMoment B raw11780step0 raw11780step0Labels := by
      have hz : ∀ j, raw11780 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11780step0 = (fun i j => raw11780 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11780step0 raw11780; decide +kernel
      have hl : raw11780step0Labels = raw11780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11780 raw11780Labels permutation520 hz
    mixedMoment B raw11780step0 raw11780step0Labels = mixedMoment B raw11780step1 raw11780step1Labels := by
      have ha : raw11780step1 = (fun i j => raw11780step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11780step1 raw11780step0; decide +kernel
      have hl : raw11780step1Labels = raw11780step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11780step0 raw11780step0Labels permutation38 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw11781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw11781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11781 raw11781Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw11781 raw11781Labels = mixedMoment B raw11781step0 raw11781step0Labels := by
      have ha : raw11781step0 = (fun i j => raw11781 (permutation252 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11781step0 raw11781; decide +kernel
      have hl : raw11781step0Labels = raw11781Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11781 raw11781Labels permutation252 permutation2
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw11782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11782 raw11782Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw11782 raw11782Labels = mixedMoment B raw11782step0 raw11782step0Labels := by
      have ha : raw11782step0 = (fun i j => raw11782 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11782step0 raw11782; decide +kernel
      have hl : raw11782step0Labels = raw11782Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11782 raw11782Labels permutation161 permutation2
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw11783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11783 raw11783Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw11783 raw11783Labels = mixedMoment B raw11783step0 raw11783step0Labels := by
      have ha : raw11783step0 = (fun i j => raw11783 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11783step0 raw11783; decide +kernel
      have hl : raw11783step0Labels = raw11783Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11783 raw11783Labels permutation161 permutation2
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw11784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11784 raw11784Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw11784 raw11784Labels = mixedMoment B raw11784step0 raw11784step0Labels := by
      have hz : ∀ j, raw11784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11784step0 = (fun i j => raw11784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11784step0 raw11784; decide +kernel
      have hl : raw11784step0Labels = raw11784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11784 raw11784Labels permutation434 hz
    mixedMoment B raw11784step0 raw11784step0Labels = mixedMoment B raw11784step1 raw11784step1Labels := by
      have ha : raw11784step1 = (fun i j => raw11784step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11784step1 raw11784step0; decide +kernel
      have hl : raw11784step1Labels = raw11784step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11784step0 raw11784step0Labels permutation35 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw11785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11785 raw11785Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw11785 raw11785Labels = mixedMoment B raw11785step0 raw11785step0Labels := by
      have hz : ∀ j, raw11785 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11785step0 = (fun i j => raw11785 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11785step0 raw11785; decide +kernel
      have hl : raw11785step0Labels = raw11785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11785 raw11785Labels permutation520 hz
    mixedMoment B raw11785step0 raw11785step0Labels = mixedMoment B raw11785step1 raw11785step1Labels := by
      have ha : raw11785step1 = (fun i j => raw11785step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11785step1 raw11785step0; decide +kernel
      have hl : raw11785step1Labels = raw11785step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11785step0 raw11785step0Labels permutation35 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw11786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11786 raw11786Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw11786 raw11786Labels = mixedMoment B raw11786step0 raw11786step0Labels := by
      have ha : raw11786step0 = (fun i j => raw11786 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11786step0 raw11786; decide +kernel
      have hl : raw11786step0Labels = raw11786Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11786 raw11786Labels permutation173 permutation2
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw11787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11787step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11787 raw11787Labels = mixedMoment B node4561 node4561Labels := by
  calc
    mixedMoment B raw11787 raw11787Labels = mixedMoment B raw11787step0 raw11787step0Labels := by
      have ha : raw11787step0 = (fun i j => raw11787 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11787step0 raw11787; decide +kernel
      have hl : raw11787step0Labels = raw11787Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11787 raw11787Labels permutation181 permutation3
    mixedMoment B raw11787step0 raw11787step0Labels = mixedMoment B raw11787step1 raw11787step1Labels := by
      have ha : raw11787step1 = raw11787step0 := by apply Matrix.ext; unfold raw11787step1 raw11787step0; decide +kernel
      have hl : raw11787step0Labels = labelEmbedding6 ∘ raw11787step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11787step0 raw11787step0Labels raw11787step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4561 node4561Labels := by rfl

def raw11788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11788 raw11788Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw11788 raw11788Labels = mixedMoment B raw11788step0 raw11788step0Labels := by
      have ha : raw11788step0 = (fun i j => raw11788 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11788step0 raw11788; decide +kernel
      have hl : raw11788step0Labels = raw11788Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11788 raw11788Labels permutation155 permutation2
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw11789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11789 raw11789Labels = mixedMoment B node5209 node5209Labels := by
  calc
    mixedMoment B raw11789 raw11789Labels = mixedMoment B raw11789step0 raw11789step0Labels := by
      have ha : raw11789step0 = (fun i j => raw11789 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11789step0 raw11789; decide +kernel
      have hl : raw11789step0Labels = raw11789Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11789 raw11789Labels permutation179 permutation2
    _ = mixedMoment B node5209 node5209Labels := by rfl

def raw11790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw11790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11790 raw11790Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw11790 raw11790Labels = mixedMoment B raw11790step0 raw11790step0Labels := by
      have hz : ∀ j, raw11790 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11790step0 = (fun i j => raw11790 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11790step0 raw11790; decide +kernel
      have hl : raw11790step0Labels = raw11790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11790 raw11790Labels permutation520 hz
    mixedMoment B raw11790step0 raw11790step0Labels = mixedMoment B raw11790step1 raw11790step1Labels := by
      have ha : raw11790step1 = (fun i j => raw11790step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11790step1 raw11790step0; decide +kernel
      have hl : raw11790step1Labels = raw11790step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11790step0 raw11790step0Labels permutation33 permutation2
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw11791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11791 raw11791Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw11791 raw11791Labels = mixedMoment B raw11791step0 raw11791step0Labels := by
      have ha : raw11791step0 = (fun i j => raw11791 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11791step0 raw11791; decide +kernel
      have hl : raw11791step0Labels = raw11791Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11791 raw11791Labels permutation171 permutation2
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw11792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11792step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11792 raw11792Labels = mixedMoment B node4561 node4561Labels := by
  calc
    mixedMoment B raw11792 raw11792Labels = mixedMoment B raw11792step0 raw11792step0Labels := by
      have ha : raw11792step0 = (fun i j => raw11792 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11792step0 raw11792; decide +kernel
      have hl : raw11792step0Labels = raw11792Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11792 raw11792Labels permutation180 permutation3
    mixedMoment B raw11792step0 raw11792step0Labels = mixedMoment B raw11792step1 raw11792step1Labels := by
      have ha : raw11792step1 = raw11792step0 := by apply Matrix.ext; unfold raw11792step1 raw11792step0; decide +kernel
      have hl : raw11792step0Labels = labelEmbedding6 ∘ raw11792step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11792step0 raw11792step0Labels raw11792step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4561 node4561Labels := by rfl

def raw11793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11793 raw11793Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw11793 raw11793Labels = mixedMoment B raw11793step0 raw11793step0Labels := by
      have ha : raw11793step0 = (fun i j => raw11793 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11793step0 raw11793; decide +kernel
      have hl : raw11793step0Labels = raw11793Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11793 raw11793Labels permutation153 permutation2
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw11794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11794 raw11794Labels = mixedMoment B node5209 node5209Labels := by
  calc
    mixedMoment B raw11794 raw11794Labels = mixedMoment B raw11794step0 raw11794step0Labels := by
      have ha : raw11794step0 = (fun i j => raw11794 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11794step0 raw11794; decide +kernel
      have hl : raw11794step0Labels = raw11794Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11794 raw11794Labels permutation177 permutation2
    _ = mixedMoment B node5209 node5209Labels := by rfl

def raw11795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw11795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11795 raw11795Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw11795 raw11795Labels = mixedMoment B raw11795step0 raw11795step0Labels := by
      have hz : ∀ j, raw11795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11795step0 = (fun i j => raw11795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11795step0 raw11795; decide +kernel
      have hl : raw11795step0Labels = raw11795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11795 raw11795Labels permutation434 hz
    mixedMoment B raw11795step0 raw11795step0Labels = mixedMoment B raw11795step1 raw11795step1Labels := by
      have ha : raw11795step1 = (fun i j => raw11795step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11795step1 raw11795step0; decide +kernel
      have hl : raw11795step1Labels = raw11795step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11795step0 raw11795step0Labels permutation33 permutation2
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw11796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw11796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11796 raw11796Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw11796 raw11796Labels = mixedMoment B raw11796step0 raw11796step0Labels := by
      have ha : raw11796step0 = (fun i j => raw11796 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11796step0 raw11796; decide +kernel
      have hl : raw11796step0Labels = raw11796Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11796 raw11796Labels permutation170 permutation2
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw11797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11797 raw11797Labels = mixedMoment B node4563 node4563Labels := by
  calc
    mixedMoment B raw11797 raw11797Labels = mixedMoment B raw11797step0 raw11797step0Labels := by
      have ha : raw11797step0 = (fun i j => raw11797 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11797step0 raw11797; decide +kernel
      have hl : raw11797step0Labels = raw11797Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11797 raw11797Labels permutation176 permutation3
    mixedMoment B raw11797step0 raw11797step0Labels = mixedMoment B raw11797step1 raw11797step1Labels := by
      have ha : raw11797step1 = raw11797step0 := by apply Matrix.ext; unfold raw11797step1 raw11797step0; decide +kernel
      have hl : raw11797step0Labels = labelEmbedding6 ∘ raw11797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11797step0 raw11797step0Labels raw11797step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4563 node4563Labels := by rfl

def raw11798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11798 raw11798Labels = mixedMoment B node5085 node5085Labels := by
  calc
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw11799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11799 raw11799Labels = mixedMoment B node5208 node5208Labels := by
  calc
    mixedMoment B raw11799 raw11799Labels = mixedMoment B raw11799step0 raw11799step0Labels := by
      have ha : raw11799step0 = (fun i j => raw11799 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11799step0 raw11799; decide +kernel
      have hl : raw11799step0Labels = raw11799Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11799 raw11799Labels permutation176 permutation2
    _ = mixedMoment B node5208 node5208Labels := by rfl

def raw11800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11800 raw11800Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw11800 raw11800Labels = mixedMoment B raw11800step0 raw11800step0Labels := by
      have hz : ∀ j, raw11800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11800step0 = (fun i j => raw11800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11800step0 raw11800; decide +kernel
      have hl : raw11800step0Labels = raw11800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11800 raw11800Labels permutation434 hz
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw11801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11801step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11801 raw11801Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw11801 raw11801Labels = mixedMoment B raw11801step0 raw11801step0Labels := by
      have hz : ∀ j, raw11801 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11801step0 = (fun i j => raw11801 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11801step0 raw11801; decide +kernel
      have hl : raw11801step0Labels = raw11801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11801 raw11801Labels permutation520 hz
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw11802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11802 raw11802Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw11802 raw11802Labels = mixedMoment B raw11802step0 raw11802step0Labels := by
      have ha : raw11802step0 = (fun i j => raw11802 (permutation427 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11802step0 raw11802; decide +kernel
      have hl : raw11802step0Labels = raw11802Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11802 raw11802Labels permutation427 permutation6
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw11803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11803 raw11803Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw11803 raw11803Labels = mixedMoment B raw11803step0 raw11803step0Labels := by
      have ha : raw11803step0 = (fun i j => raw11803 (permutation427 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11803step0 raw11803; decide +kernel
      have hl : raw11803step0Labels = raw11803Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11803 raw11803Labels permutation427 permutation6
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw11804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11804step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11804 raw11804Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw11804 raw11804Labels = mixedMoment B raw11804step0 raw11804step0Labels := by
      have hz : ∀ j, raw11804 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11804step0 = (fun i j => raw11804 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11804step0 raw11804; decide +kernel
      have hl : raw11804step0Labels = raw11804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11804 raw11804Labels permutation434 hz
    mixedMoment B raw11804step0 raw11804step0Labels = mixedMoment B raw11804step1 raw11804step1Labels := by
      have ha : raw11804step1 = (fun i j => raw11804step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11804step1 raw11804step0; decide +kernel
      have hl : raw11804step1Labels = raw11804step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11804step0 raw11804step0Labels permutation103 permutation6
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw11805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11805 raw11805Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw11805 raw11805Labels = mixedMoment B raw11805step0 raw11805step0Labels := by
      have hz : ∀ j, raw11805 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11805step0 = (fun i j => raw11805 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11805step0 raw11805; decide +kernel
      have hl : raw11805step0Labels = raw11805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11805 raw11805Labels permutation520 hz
    mixedMoment B raw11805step0 raw11805step0Labels = mixedMoment B raw11805step1 raw11805step1Labels := by
      have ha : raw11805step1 = (fun i j => raw11805step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11805step1 raw11805step0; decide +kernel
      have hl : raw11805step1Labels = raw11805step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11805step0 raw11805step0Labels permutation103 permutation6
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw11806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11806 raw11806Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw11806 raw11806Labels = mixedMoment B raw11806step0 raw11806step0Labels := by
      have ha : raw11806step0 = (fun i j => raw11806 (permutation427 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11806step0 raw11806; decide +kernel
      have hl : raw11806step0Labels = raw11806Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11806 raw11806Labels permutation427 permutation6
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw11807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11807 raw11807Labels = mixedMoment B node1183 node1183Labels := by
  calc
    mixedMoment B raw11807 raw11807Labels = mixedMoment B raw11807step0 raw11807step0Labels := by
      have ha : raw11807step0 = (fun i j => raw11807 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11807step0 raw11807; decide +kernel
      have hl : raw11807step0Labels = raw11807Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11807 raw11807Labels permutation197 permutation3
    _ = mixedMoment B node1183 node1183Labels := by rfl

def raw11808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11808 raw11808Labels = mixedMoment B node2836 node2836Labels := by
  calc
    mixedMoment B raw11808 raw11808Labels = mixedMoment B raw11808step0 raw11808step0Labels := by
      have ha : raw11808step0 = (fun i j => raw11808 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11808step0 raw11808; decide +kernel
      have hl : raw11808step0Labels = raw11808Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11808 raw11808Labels permutation197 permutation3
    _ = mixedMoment B node2836 node2836Labels := by rfl

def raw11809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11809 raw11809Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw11809 raw11809Labels = mixedMoment B raw11809step0 raw11809step0Labels := by
      have hz : ∀ j, raw11809 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11809step0 = (fun i j => raw11809 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11809step0 raw11809; decide +kernel
      have hl : raw11809step0Labels = raw11809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11809 raw11809Labels permutation434 hz
    mixedMoment B raw11809step0 raw11809step0Labels = mixedMoment B raw11809step1 raw11809step1Labels := by
      have ha : raw11809step1 = (fun i j => raw11809step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11809step1 raw11809step0; decide +kernel
      have hl : raw11809step1Labels = raw11809step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11809step0 raw11809step0Labels permutation43 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw11810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11810step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11810 raw11810Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw11810 raw11810Labels = mixedMoment B raw11810step0 raw11810step0Labels := by
      have hz : ∀ j, raw11810 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11810step0 = (fun i j => raw11810 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11810step0 raw11810; decide +kernel
      have hl : raw11810step0Labels = raw11810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11810 raw11810Labels permutation520 hz
    mixedMoment B raw11810step0 raw11810step0Labels = mixedMoment B raw11810step1 raw11810step1Labels := by
      have ha : raw11810step1 = (fun i j => raw11810step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11810step1 raw11810step0; decide +kernel
      have hl : raw11810step1Labels = raw11810step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11810step0 raw11810step0Labels permutation43 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw11811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11811 raw11811Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw11811 raw11811Labels = mixedMoment B raw11811step0 raw11811step0Labels := by
      have ha : raw11811step0 = (fun i j => raw11811 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11811step0 raw11811; decide +kernel
      have hl : raw11811step0Labels = raw11811Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11811 raw11811Labels permutation197 permutation3
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw11812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11812 raw11812Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw11812 raw11812Labels = mixedMoment B raw11812step0 raw11812step0Labels := by
      have ha : raw11812step0 = (fun i j => raw11812 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11812step0 raw11812; decide +kernel
      have hl : raw11812step0Labels = raw11812Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11812 raw11812Labels permutation156 permutation3
    _ = mixedMoment B node1260 node1260Labels := by rfl

def raw11813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11813 raw11813Labels = mixedMoment B node2996 node2996Labels := by
  calc
    mixedMoment B raw11813 raw11813Labels = mixedMoment B raw11813step0 raw11813step0Labels := by
      have ha : raw11813step0 = (fun i j => raw11813 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11813step0 raw11813; decide +kernel
      have hl : raw11813step0Labels = raw11813Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11813 raw11813Labels permutation156 permutation3
    _ = mixedMoment B node2996 node2996Labels := by rfl

def raw11814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11814step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11814step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11814 raw11814Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw11814 raw11814Labels = mixedMoment B raw11814step0 raw11814step0Labels := by
      have hz : ∀ j, raw11814 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11814step0 = (fun i j => raw11814 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11814step0 raw11814; decide +kernel
      have hl : raw11814step0Labels = raw11814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11814 raw11814Labels permutation434 hz
    mixedMoment B raw11814step0 raw11814step0Labels = mixedMoment B raw11814step1 raw11814step1Labels := by
      have ha : raw11814step1 = (fun i j => raw11814step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11814step1 raw11814step0; decide +kernel
      have hl : raw11814step1Labels = raw11814step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11814step0 raw11814step0Labels permutation33 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw11815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11815 raw11815Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw11815 raw11815Labels = mixedMoment B raw11815step0 raw11815step0Labels := by
      have hz : ∀ j, raw11815 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11815step0 = (fun i j => raw11815 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11815step0 raw11815; decide +kernel
      have hl : raw11815step0Labels = raw11815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11815 raw11815Labels permutation520 hz
    mixedMoment B raw11815step0 raw11815step0Labels = mixedMoment B raw11815step1 raw11815step1Labels := by
      have ha : raw11815step1 = (fun i j => raw11815step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11815step1 raw11815step0; decide +kernel
      have hl : raw11815step1Labels = raw11815step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11815step0 raw11815step0Labels permutation33 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw11816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11816 raw11816Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw11816 raw11816Labels = mixedMoment B raw11816step0 raw11816step0Labels := by
      have ha : raw11816step0 = (fun i j => raw11816 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11816step0 raw11816; decide +kernel
      have hl : raw11816step0Labels = raw11816Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11816 raw11816Labels permutation246 permutation3
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw11817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11817 raw11817Labels = mixedMoment B node1178 node1178Labels := by
  calc
    mixedMoment B raw11817 raw11817Labels = mixedMoment B raw11817step0 raw11817step0Labels := by
      have ha : raw11817step0 = (fun i j => raw11817 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11817step0 raw11817; decide +kernel
      have hl : raw11817step0Labels = raw11817Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11817 raw11817Labels permutation181 permutation3
    _ = mixedMoment B node1178 node1178Labels := by rfl

def raw11818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11818 raw11818Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw11818 raw11818Labels = mixedMoment B raw11818step0 raw11818step0Labels := by
      have ha : raw11818step0 = (fun i j => raw11818 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11818step0 raw11818; decide +kernel
      have hl : raw11818step0Labels = raw11818Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11818 raw11818Labels permutation157 permutation3
    _ = mixedMoment B node2974 node2974Labels := by rfl

def raw11819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11819 raw11819Labels = mixedMoment B node2833 node2833Labels := by
  calc
    mixedMoment B raw11819 raw11819Labels = mixedMoment B raw11819step0 raw11819step0Labels := by
      have ha : raw11819step0 = (fun i j => raw11819 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11819step0 raw11819; decide +kernel
      have hl : raw11819step0Labels = raw11819Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11819 raw11819Labels permutation181 permutation3
    _ = mixedMoment B node2833 node2833Labels := by rfl

def raw11820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw11820step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11820 raw11820Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw11820 raw11820Labels = mixedMoment B raw11820step0 raw11820step0Labels := by
      have hz : ∀ j, raw11820 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11820step0 = (fun i j => raw11820 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11820step0 raw11820; decide +kernel
      have hl : raw11820step0Labels = raw11820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11820 raw11820Labels permutation520 hz
    mixedMoment B raw11820step0 raw11820step0Labels = mixedMoment B raw11820step1 raw11820step1Labels := by
      have ha : raw11820step1 = (fun i j => raw11820step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11820step1 raw11820step0; decide +kernel
      have hl : raw11820step1Labels = raw11820step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11820step0 raw11820step0Labels permutation39 permutation3
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw11821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw11821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11821 raw11821Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw11821 raw11821Labels = mixedMoment B raw11821step0 raw11821step0Labels := by
      have ha : raw11821step0 = (fun i j => raw11821 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11821step0 raw11821; decide +kernel
      have hl : raw11821step0Labels = raw11821Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11821 raw11821Labels permutation195 permutation3
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw11822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11822 raw11822Labels = mixedMoment B node1178 node1178Labels := by
  calc
    mixedMoment B raw11822 raw11822Labels = mixedMoment B raw11822step0 raw11822step0Labels := by
      have ha : raw11822step0 = (fun i j => raw11822 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11822step0 raw11822; decide +kernel
      have hl : raw11822step0Labels = raw11822Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11822 raw11822Labels permutation180 permutation3
    _ = mixedMoment B node1178 node1178Labels := by rfl

def raw11823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11823 raw11823Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw11823 raw11823Labels = mixedMoment B raw11823step0 raw11823step0Labels := by
      have ha : raw11823step0 = (fun i j => raw11823 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11823step0 raw11823; decide +kernel
      have hl : raw11823step0Labels = raw11823Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11823 raw11823Labels permutation156 permutation3
    _ = mixedMoment B node2974 node2974Labels := by rfl

def raw11824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11824 raw11824Labels = mixedMoment B node2833 node2833Labels := by
  calc
    mixedMoment B raw11824 raw11824Labels = mixedMoment B raw11824step0 raw11824step0Labels := by
      have ha : raw11824step0 = (fun i j => raw11824 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11824step0 raw11824; decide +kernel
      have hl : raw11824step0Labels = raw11824Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11824 raw11824Labels permutation180 permutation3
    _ = mixedMoment B node2833 node2833Labels := by rfl

def raw11825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw11825step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11825 raw11825Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw11825 raw11825Labels = mixedMoment B raw11825step0 raw11825step0Labels := by
      have hz : ∀ j, raw11825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11825step0 = (fun i j => raw11825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11825step0 raw11825; decide +kernel
      have hl : raw11825step0Labels = raw11825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11825 raw11825Labels permutation434 hz
    mixedMoment B raw11825step0 raw11825step0Labels = mixedMoment B raw11825step1 raw11825step1Labels := by
      have ha : raw11825step1 = (fun i j => raw11825step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11825step1 raw11825step0; decide +kernel
      have hl : raw11825step1Labels = raw11825step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11825step0 raw11825step0Labels permutation39 permutation3
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw11826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw11826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw11826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11826 raw11826Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw11826 raw11826Labels = mixedMoment B raw11826step0 raw11826step0Labels := by
      have ha : raw11826step0 = (fun i j => raw11826 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11826step0 raw11826; decide +kernel
      have hl : raw11826step0Labels = raw11826Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11826 raw11826Labels permutation194 permutation3
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw11827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11827 raw11827Labels = mixedMoment B node1180 node1180Labels := by
  calc
    mixedMoment B raw11827 raw11827Labels = mixedMoment B raw11827step0 raw11827step0Labels := by
      have ha : raw11827step0 = (fun i j => raw11827 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11827step0 raw11827; decide +kernel
      have hl : raw11827step0Labels = raw11827Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11827 raw11827Labels permutation176 permutation3
    _ = mixedMoment B node1180 node1180Labels := by rfl

def raw11828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11828 raw11828Labels = mixedMoment B node2976 node2976Labels := by
  calc
    mixedMoment B raw11828 raw11828Labels = mixedMoment B raw11828step0 raw11828step0Labels := by
      have ha : raw11828step0 = (fun i j => raw11828 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11828step0 raw11828; decide +kernel
      have hl : raw11828step0Labels = raw11828Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11828 raw11828Labels permutation152 permutation3
    _ = mixedMoment B node2976 node2976Labels := by rfl

def raw11829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11829 raw11829Labels = mixedMoment B node2834 node2834Labels := by
  calc
    mixedMoment B raw11829 raw11829Labels = mixedMoment B raw11829step0 raw11829step0Labels := by
      have ha : raw11829step0 = (fun i j => raw11829 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11829step0 raw11829; decide +kernel
      have hl : raw11829step0Labels = raw11829Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11829 raw11829Labels permutation176 permutation3
    _ = mixedMoment B node2834 node2834Labels := by rfl

def raw11830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11830 raw11830Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw11830 raw11830Labels = mixedMoment B raw11830step0 raw11830step0Labels := by
      have hz : ∀ j, raw11830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11830step0 = (fun i j => raw11830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11830step0 raw11830; decide +kernel
      have hl : raw11830step0Labels = raw11830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11830 raw11830Labels permutation434 hz
    mixedMoment B raw11830step0 raw11830step0Labels = mixedMoment B raw11830step1 raw11830step1Labels := by
      have ha : raw11830step1 = (fun i j => raw11830step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11830step1 raw11830step0; decide +kernel
      have hl : raw11830step1Labels = raw11830step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11830step0 raw11830step0Labels permutation38 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw11831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11831step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11831 raw11831Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw11831 raw11831Labels = mixedMoment B raw11831step0 raw11831step0Labels := by
      have hz : ∀ j, raw11831 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11831step0 = (fun i j => raw11831 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11831step0 raw11831; decide +kernel
      have hl : raw11831step0Labels = raw11831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11831 raw11831Labels permutation520 hz
    mixedMoment B raw11831step0 raw11831step0Labels = mixedMoment B raw11831step1 raw11831step1Labels := by
      have ha : raw11831step1 = (fun i j => raw11831step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11831step1 raw11831step0; decide +kernel
      have hl : raw11831step1Labels = raw11831step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11831step0 raw11831step0Labels permutation38 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw11832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11832Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11832step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11832 raw11832Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw11832 raw11832Labels = mixedMoment B raw11832step0 raw11832step0Labels := by
      have ha : raw11832step0 = (fun i j => raw11832 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11832step0 raw11832; decide +kernel
      have hl : raw11832step0Labels = raw11832Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11832 raw11832Labels permutation161 permutation7
    mixedMoment B raw11832step0 raw11832step0Labels = mixedMoment B raw11832step1 raw11832step1Labels := by
      have ha : raw11832step1 = -raw11832step0 := by apply Matrix.ext; change ∀ i j, raw11832step1 i j = -(raw11832step0 i j); unfold raw11832step1 raw11832step0; decide +kernel
      have hl : raw11832step1Labels = raw11832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11832step1 raw11832step1Labels = mixedMoment B raw11832step2 raw11832step2Labels := by
      have ha : raw11832step2 = raw11832step1 := by apply Matrix.ext; unfold raw11832step2 raw11832step1; decide +kernel
      have hl : raw11832step1Labels = labelEmbedding1 ∘ raw11832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11832step1 raw11832step1Labels raw11832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw11833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11833Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11833step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11833step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11833 raw11833Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11833 raw11833Labels = mixedMoment B raw11833step0 raw11833step0Labels := by
      have ha : raw11833step0 = (fun i j => raw11833 (permutation361 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11833step0 raw11833; decide +kernel
      have hl : raw11833step0Labels = raw11833Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11833 raw11833Labels permutation361 permutation5
    mixedMoment B raw11833step0 raw11833step0Labels = mixedMoment B raw11833step1 raw11833step1Labels := by
      have ha : raw11833step1 = -raw11833step0 := by apply Matrix.ext; change ∀ i j, raw11833step1 i j = -(raw11833step0 i j); unfold raw11833step1 raw11833step0; decide +kernel
      have hl : raw11833step1Labels = raw11833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11833step1 raw11833step1Labels = mixedMoment B raw11833step2 raw11833step2Labels := by
      have ha : raw11833step2 = raw11833step1 := by apply Matrix.ext; unfold raw11833step2 raw11833step1; decide +kernel
      have hl : raw11833step1Labels = labelEmbedding1 ∘ raw11833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11833step1 raw11833step1Labels raw11833step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw11834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11834Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11834step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11834step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11834step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11834step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11834 raw11834Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw11834 raw11834Labels = mixedMoment B raw11834step0 raw11834step0Labels := by
      have hz : ∀ j, raw11834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11834step0 = (fun i j => raw11834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11834step0 raw11834; decide +kernel
      have hl : raw11834step0Labels = raw11834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11834 raw11834Labels permutation434 hz
    mixedMoment B raw11834step0 raw11834step0Labels = mixedMoment B raw11834step1 raw11834step1Labels := by
      have ha : raw11834step1 = (fun i j => raw11834step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11834step1 raw11834step0; decide +kernel
      have hl : raw11834step1Labels = raw11834step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11834step0 raw11834step0Labels permutation35 permutation7
    mixedMoment B raw11834step1 raw11834step1Labels = mixedMoment B raw11834step2 raw11834step2Labels := by
      have ha : raw11834step2 = -raw11834step1 := by apply Matrix.ext; change ∀ i j, raw11834step2 i j = -(raw11834step1 i j); unfold raw11834step2 raw11834step1; decide +kernel
      have hl : raw11834step2Labels = raw11834step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11834step2 raw11834step2Labels = mixedMoment B raw11834step3 raw11834step3Labels := by
      have ha : raw11834step3 = raw11834step2 := by apply Matrix.ext; unfold raw11834step3 raw11834step2; decide +kernel
      have hl : raw11834step2Labels = labelEmbedding1 ∘ raw11834step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11834step2 raw11834step2Labels raw11834step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw11835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11835Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11835step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11835step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11835step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11835step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11835step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11835 raw11835Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw11835 raw11835Labels = mixedMoment B raw11835step0 raw11835step0Labels := by
      have hz : ∀ j, raw11835 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11835step0 = (fun i j => raw11835 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11835step0 raw11835; decide +kernel
      have hl : raw11835step0Labels = raw11835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11835 raw11835Labels permutation520 hz
    mixedMoment B raw11835step0 raw11835step0Labels = mixedMoment B raw11835step1 raw11835step1Labels := by
      have ha : raw11835step1 = (fun i j => raw11835step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11835step1 raw11835step0; decide +kernel
      have hl : raw11835step1Labels = raw11835step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11835step0 raw11835step0Labels permutation35 permutation7
    mixedMoment B raw11835step1 raw11835step1Labels = mixedMoment B raw11835step2 raw11835step2Labels := by
      have ha : raw11835step2 = -raw11835step1 := by apply Matrix.ext; change ∀ i j, raw11835step2 i j = -(raw11835step1 i j); unfold raw11835step2 raw11835step1; decide +kernel
      have hl : raw11835step2Labels = raw11835step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11835step2 raw11835step2Labels = mixedMoment B raw11835step3 raw11835step3Labels := by
      have ha : raw11835step3 = raw11835step2 := by apply Matrix.ext; unfold raw11835step3 raw11835step2; decide +kernel
      have hl : raw11835step2Labels = labelEmbedding1 ∘ raw11835step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11835step2 raw11835step2Labels raw11835step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw11836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw11836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11836step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11836step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11836 raw11836Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw11836 raw11836Labels = mixedMoment B raw11836step0 raw11836step0Labels := by
      have ha : raw11836step0 = (fun i j => raw11836 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11836step0 raw11836; decide +kernel
      have hl : raw11836step0Labels = raw11836Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11836 raw11836Labels permutation161 permutation7
    mixedMoment B raw11836step0 raw11836step0Labels = mixedMoment B raw11836step1 raw11836step1Labels := by
      have ha : raw11836step1 = -raw11836step0 := by apply Matrix.ext; change ∀ i j, raw11836step1 i j = -(raw11836step0 i j); unfold raw11836step1 raw11836step0; decide +kernel
      have hl : raw11836step1Labels = raw11836step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11836step1 raw11836step1Labels = mixedMoment B raw11836step2 raw11836step2Labels := by
      have ha : raw11836step2 = raw11836step1 := by apply Matrix.ext; unfold raw11836step2 raw11836step1; decide +kernel
      have hl : raw11836step1Labels = labelEmbedding1 ∘ raw11836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11836step1 raw11836step1Labels raw11836step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw11837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11837step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11837step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11837step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11837 raw11837Labels = mixedMoment B node3239 node3239Labels := by
  calc
    mixedMoment B raw11837 raw11837Labels = mixedMoment B raw11837step0 raw11837step0Labels := by
      have ha : raw11837step0 = (fun i j => raw11837 (permutation197 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11837step0 raw11837; decide +kernel
      have hl : raw11837step0Labels = raw11837Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11837 raw11837Labels permutation197 permutation5
    mixedMoment B raw11837step0 raw11837step0Labels = mixedMoment B raw11837step1 raw11837step1Labels := by
      have ha : raw11837step1 = -raw11837step0 := by apply Matrix.ext; change ∀ i j, raw11837step1 i j = -(raw11837step0 i j); unfold raw11837step1 raw11837step0; decide +kernel
      have hl : raw11837step1Labels = raw11837step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11837step1 raw11837step1Labels = mixedMoment B raw11837step2 raw11837step2Labels := by
      have ha : raw11837step2 = raw11837step1 := by apply Matrix.ext; unfold raw11837step2 raw11837step1; decide +kernel
      have hl : raw11837step1Labels = labelEmbedding1 ∘ raw11837step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11837step1 raw11837step1Labels raw11837step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3239 node3239Labels := by rfl

def raw11838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11838step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11838 raw11838Labels = mixedMoment B node2834 node2834Labels := by
  calc
    mixedMoment B raw11838 raw11838Labels = mixedMoment B raw11838step0 raw11838step0Labels := by
      have ha : raw11838step0 = (fun i j => raw11838 (permutation364 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11838step0 raw11838; decide +kernel
      have hl : raw11838step0Labels = raw11838Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11838 raw11838Labels permutation364 permutation5
    mixedMoment B raw11838step0 raw11838step0Labels = mixedMoment B raw11838step1 raw11838step1Labels := by
      have ha : raw11838step1 = -raw11838step0 := by apply Matrix.ext; change ∀ i j, raw11838step1 i j = -(raw11838step0 i j); unfold raw11838step1 raw11838step0; decide +kernel
      have hl : raw11838step1Labels = raw11838step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11838step1 raw11838step1Labels = mixedMoment B raw11838step2 raw11838step2Labels := by
      have ha : raw11838step2 = raw11838step1 := by apply Matrix.ext; unfold raw11838step2 raw11838step1; decide +kernel
      have hl : raw11838step1Labels = labelEmbedding1 ∘ raw11838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11838step1 raw11838step1Labels raw11838step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2834 node2834Labels := by rfl

def raw11839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11839step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11839step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11839step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11839step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11839step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11839 raw11839Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw11839 raw11839Labels = mixedMoment B raw11839step0 raw11839step0Labels := by
      have hz : ∀ j, raw11839 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11839step0 = (fun i j => raw11839 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11839step0 raw11839; decide +kernel
      have hl : raw11839step0Labels = raw11839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11839 raw11839Labels permutation434 hz
    mixedMoment B raw11839step0 raw11839step0Labels = mixedMoment B raw11839step1 raw11839step1Labels := by
      have ha : raw11839step1 = (fun i j => raw11839step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11839step1 raw11839step0; decide +kernel
      have hl : raw11839step1Labels = raw11839step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11839step0 raw11839step0Labels permutation35 permutation7
    mixedMoment B raw11839step1 raw11839step1Labels = mixedMoment B raw11839step2 raw11839step2Labels := by
      have ha : raw11839step2 = -raw11839step1 := by apply Matrix.ext; change ∀ i j, raw11839step2 i j = -(raw11839step1 i j); unfold raw11839step2 raw11839step1; decide +kernel
      have hl : raw11839step2Labels = raw11839step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11839step2 raw11839step2Labels = mixedMoment B raw11839step3 raw11839step3Labels := by
      have ha : raw11839step3 = raw11839step2 := by apply Matrix.ext; unfold raw11839step3 raw11839step2; decide +kernel
      have hl : raw11839step2Labels = labelEmbedding1 ∘ raw11839step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11839step2 raw11839step2Labels raw11839step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw11840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11840step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11840step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11840step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11840 raw11840Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw11840 raw11840Labels = mixedMoment B raw11840step0 raw11840step0Labels := by
      have hz : ∀ j, raw11840 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11840step0 = (fun i j => raw11840 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11840step0 raw11840; decide +kernel
      have hl : raw11840step0Labels = raw11840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11840 raw11840Labels permutation520 hz
    mixedMoment B raw11840step0 raw11840step0Labels = mixedMoment B raw11840step1 raw11840step1Labels := by
      have ha : raw11840step1 = (fun i j => raw11840step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11840step1 raw11840step0; decide +kernel
      have hl : raw11840step1Labels = raw11840step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11840step0 raw11840step0Labels permutation35 permutation7
    mixedMoment B raw11840step1 raw11840step1Labels = mixedMoment B raw11840step2 raw11840step2Labels := by
      have ha : raw11840step2 = -raw11840step1 := by apply Matrix.ext; change ∀ i j, raw11840step2 i j = -(raw11840step1 i j); unfold raw11840step2 raw11840step1; decide +kernel
      have hl : raw11840step2Labels = raw11840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11840step2 raw11840step2Labels = mixedMoment B raw11840step3 raw11840step3Labels := by
      have ha : raw11840step3 = raw11840step2 := by apply Matrix.ext; unfold raw11840step3 raw11840step2; decide +kernel
      have hl : raw11840step2Labels = labelEmbedding1 ∘ raw11840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11840step2 raw11840step2Labels raw11840step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw11841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11841Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw11841step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11841step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11841step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11841 raw11841Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw11841 raw11841Labels = mixedMoment B raw11841step0 raw11841step0Labels := by
      have ha : raw11841step0 = (fun i j => raw11841 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11841step0 raw11841; decide +kernel
      have hl : raw11841step0Labels = raw11841Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11841 raw11841Labels permutation161 permutation7
    mixedMoment B raw11841step0 raw11841step0Labels = mixedMoment B raw11841step1 raw11841step1Labels := by
      have ha : raw11841step1 = -raw11841step0 := by apply Matrix.ext; change ∀ i j, raw11841step1 i j = -(raw11841step0 i j); unfold raw11841step1 raw11841step0; decide +kernel
      have hl : raw11841step1Labels = raw11841step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11841step1 raw11841step1Labels = mixedMoment B raw11841step2 raw11841step2Labels := by
      have ha : raw11841step2 = raw11841step1 := by apply Matrix.ext; unfold raw11841step2 raw11841step1; decide +kernel
      have hl : raw11841step1Labels = labelEmbedding1 ∘ raw11841step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11841step1 raw11841step1Labels raw11841step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3567 node3567Labels := by rfl

def raw11842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11842Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11842step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11842step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11842 raw11842Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw11842 raw11842Labels = mixedMoment B raw11842step0 raw11842step0Labels := by
      have ha : raw11842step0 = (fun i j => raw11842 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11842step0 raw11842; decide +kernel
      have hl : raw11842step0Labels = raw11842Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11842 raw11842Labels permutation161 permutation7
    mixedMoment B raw11842step0 raw11842step0Labels = mixedMoment B raw11842step1 raw11842step1Labels := by
      have ha : raw11842step1 = -raw11842step0 := by apply Matrix.ext; change ∀ i j, raw11842step1 i j = -(raw11842step0 i j); unfold raw11842step1 raw11842step0; decide +kernel
      have hl : raw11842step1Labels = raw11842step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11842step1 raw11842step1Labels = mixedMoment B raw11842step2 raw11842step2Labels := by
      have ha : raw11842step2 = raw11842step1 := by apply Matrix.ext; unfold raw11842step2 raw11842step1; decide +kernel
      have hl : raw11842step1Labels = labelEmbedding1 ∘ raw11842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11842step1 raw11842step1Labels raw11842step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw11843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11843Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11843step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11843step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11843step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11843 raw11843Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw11843 raw11843Labels = mixedMoment B raw11843step0 raw11843step0Labels := by
      have ha : raw11843step0 = (fun i j => raw11843 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11843step0 raw11843; decide +kernel
      have hl : raw11843step0Labels = raw11843Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11843 raw11843Labels permutation161 permutation7
    mixedMoment B raw11843step0 raw11843step0Labels = mixedMoment B raw11843step1 raw11843step1Labels := by
      have ha : raw11843step1 = -raw11843step0 := by apply Matrix.ext; change ∀ i j, raw11843step1 i j = -(raw11843step0 i j); unfold raw11843step1 raw11843step0; decide +kernel
      have hl : raw11843step1Labels = raw11843step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11843step1 raw11843step1Labels = mixedMoment B raw11843step2 raw11843step2Labels := by
      have ha : raw11843step2 = raw11843step1 := by apply Matrix.ext; unfold raw11843step2 raw11843step1; decide +kernel
      have hl : raw11843step1Labels = labelEmbedding1 ∘ raw11843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11843step1 raw11843step1Labels raw11843step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

def raw11844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11844Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11844step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11844step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11844step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11844step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11844step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11844 raw11844Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw11844 raw11844Labels = mixedMoment B raw11844step0 raw11844step0Labels := by
      have hz : ∀ j, raw11844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11844step0 = (fun i j => raw11844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11844step0 raw11844; decide +kernel
      have hl : raw11844step0Labels = raw11844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11844 raw11844Labels permutation434 hz
    mixedMoment B raw11844step0 raw11844step0Labels = mixedMoment B raw11844step1 raw11844step1Labels := by
      have ha : raw11844step1 = (fun i j => raw11844step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11844step1 raw11844step0; decide +kernel
      have hl : raw11844step1Labels = raw11844step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11844step0 raw11844step0Labels permutation35 permutation7
    mixedMoment B raw11844step1 raw11844step1Labels = mixedMoment B raw11844step2 raw11844step2Labels := by
      have ha : raw11844step2 = -raw11844step1 := by apply Matrix.ext; change ∀ i j, raw11844step2 i j = -(raw11844step1 i j); unfold raw11844step2 raw11844step1; decide +kernel
      have hl : raw11844step2Labels = raw11844step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11844step2 raw11844step2Labels = mixedMoment B raw11844step3 raw11844step3Labels := by
      have ha : raw11844step3 = raw11844step2 := by apply Matrix.ext; unfold raw11844step3 raw11844step2; decide +kernel
      have hl : raw11844step2Labels = labelEmbedding1 ∘ raw11844step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11844step2 raw11844step2Labels raw11844step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw11845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11845Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11845step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11845step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11845step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11845step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11845 raw11845Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw11845 raw11845Labels = mixedMoment B raw11845step0 raw11845step0Labels := by
      have hz : ∀ j, raw11845 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11845step0 = (fun i j => raw11845 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11845step0 raw11845; decide +kernel
      have hl : raw11845step0Labels = raw11845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11845 raw11845Labels permutation520 hz
    mixedMoment B raw11845step0 raw11845step0Labels = mixedMoment B raw11845step1 raw11845step1Labels := by
      have ha : raw11845step1 = (fun i j => raw11845step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11845step1 raw11845step0; decide +kernel
      have hl : raw11845step1Labels = raw11845step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11845step0 raw11845step0Labels permutation35 permutation7
    mixedMoment B raw11845step1 raw11845step1Labels = mixedMoment B raw11845step2 raw11845step2Labels := by
      have ha : raw11845step2 = -raw11845step1 := by apply Matrix.ext; change ∀ i j, raw11845step2 i j = -(raw11845step1 i j); unfold raw11845step2 raw11845step1; decide +kernel
      have hl : raw11845step2Labels = raw11845step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11845step2 raw11845step2Labels = mixedMoment B raw11845step3 raw11845step3Labels := by
      have ha : raw11845step3 = raw11845step2 := by apply Matrix.ext; unfold raw11845step3 raw11845step2; decide +kernel
      have hl : raw11845step2Labels = labelEmbedding1 ∘ raw11845step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11845step2 raw11845step2Labels raw11845step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw11846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11846Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11846step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11846step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11846step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11846 raw11846Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw11846 raw11846Labels = mixedMoment B raw11846step0 raw11846step0Labels := by
      have ha : raw11846step0 = (fun i j => raw11846 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11846step0 raw11846; decide +kernel
      have hl : raw11846step0Labels = raw11846Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11846 raw11846Labels permutation161 permutation7
    mixedMoment B raw11846step0 raw11846step0Labels = mixedMoment B raw11846step1 raw11846step1Labels := by
      have ha : raw11846step1 = -raw11846step0 := by apply Matrix.ext; change ∀ i j, raw11846step1 i j = -(raw11846step0 i j); unfold raw11846step1 raw11846step0; decide +kernel
      have hl : raw11846step1Labels = raw11846step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11846step1 raw11846step1Labels = mixedMoment B raw11846step2 raw11846step2Labels := by
      have ha : raw11846step2 = raw11846step1 := by apply Matrix.ext; unfold raw11846step2 raw11846step1; decide +kernel
      have hl : raw11846step1Labels = labelEmbedding1 ∘ raw11846step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11846step1 raw11846step1Labels raw11846step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

def raw11847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11847Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11847step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11847step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11847step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11847step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11847 raw11847Labels = mixedMoment B node3238 node3238Labels := by
  calc
    mixedMoment B raw11847 raw11847Labels = mixedMoment B raw11847step0 raw11847step0Labels := by
      have ha : raw11847step0 = (fun i j => raw11847 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11847step0 raw11847; decide +kernel
      have hl : raw11847step0Labels = raw11847Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11847 raw11847Labels permutation195 permutation5
    mixedMoment B raw11847step0 raw11847step0Labels = mixedMoment B raw11847step1 raw11847step1Labels := by
      have ha : raw11847step1 = -raw11847step0 := by apply Matrix.ext; change ∀ i j, raw11847step1 i j = -(raw11847step0 i j); unfold raw11847step1 raw11847step0; decide +kernel
      have hl : raw11847step1Labels = raw11847step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11847step1 raw11847step1Labels = mixedMoment B raw11847step2 raw11847step2Labels := by
      have ha : raw11847step2 = raw11847step1 := by apply Matrix.ext; unfold raw11847step2 raw11847step1; decide +kernel
      have hl : raw11847step1Labels = labelEmbedding1 ∘ raw11847step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11847step1 raw11847step1Labels raw11847step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3238 node3238Labels := by rfl

def raw11848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11848Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw11848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11848step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11848step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11848 raw11848Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw11848 raw11848Labels = mixedMoment B raw11848step0 raw11848step0Labels := by
      have ha : raw11848step0 = (fun i j => raw11848 (permutation167 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11848step0 raw11848; decide +kernel
      have hl : raw11848step0Labels = raw11848Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11848 raw11848Labels permutation167 permutation7
    mixedMoment B raw11848step0 raw11848step0Labels = mixedMoment B raw11848step1 raw11848step1Labels := by
      have ha : raw11848step1 = -raw11848step0 := by apply Matrix.ext; change ∀ i j, raw11848step1 i j = -(raw11848step0 i j); unfold raw11848step1 raw11848step0; decide +kernel
      have hl : raw11848step1Labels = raw11848step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11848step1 raw11848step1Labels = mixedMoment B raw11848step2 raw11848step2Labels := by
      have ha : raw11848step2 = raw11848step1 := by apply Matrix.ext; unfold raw11848step2 raw11848step1; decide +kernel
      have hl : raw11848step1Labels = labelEmbedding1 ∘ raw11848step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11848step1 raw11848step1Labels raw11848step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw11849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11849Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11849step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11849step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11849step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11849 raw11849Labels = mixedMoment B node2833 node2833Labels := by
  calc
    mixedMoment B raw11849 raw11849Labels = mixedMoment B raw11849step0 raw11849step0Labels := by
      have ha : raw11849step0 = (fun i j => raw11849 (permutation362 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11849step0 raw11849; decide +kernel
      have hl : raw11849step0Labels = raw11849Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11849 raw11849Labels permutation362 permutation5
    mixedMoment B raw11849step0 raw11849step0Labels = mixedMoment B raw11849step1 raw11849step1Labels := by
      have ha : raw11849step1 = -raw11849step0 := by apply Matrix.ext; change ∀ i j, raw11849step1 i j = -(raw11849step0 i j); unfold raw11849step1 raw11849step0; decide +kernel
      have hl : raw11849step1Labels = raw11849step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11849step1 raw11849step1Labels = mixedMoment B raw11849step2 raw11849step2Labels := by
      have ha : raw11849step2 = raw11849step1 := by apply Matrix.ext; unfold raw11849step2 raw11849step1; decide +kernel
      have hl : raw11849step1Labels = labelEmbedding1 ∘ raw11849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11849step1 raw11849step1Labels raw11849step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2833 node2833Labels := by rfl

def raw11850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11850Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw11850step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw11850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11850step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11850step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11850step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11850 raw11850Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw11850 raw11850Labels = mixedMoment B raw11850step0 raw11850step0Labels := by
      have hz : ∀ j, raw11850 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11850step0 = (fun i j => raw11850 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11850step0 raw11850; decide +kernel
      have hl : raw11850step0Labels = raw11850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11850 raw11850Labels permutation520 hz
    mixedMoment B raw11850step0 raw11850step0Labels = mixedMoment B raw11850step1 raw11850step1Labels := by
      have ha : raw11850step1 = (fun i j => raw11850step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11850step1 raw11850step0; decide +kernel
      have hl : raw11850step1Labels = raw11850step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11850step0 raw11850step0Labels permutation35 permutation7
    mixedMoment B raw11850step1 raw11850step1Labels = mixedMoment B raw11850step2 raw11850step2Labels := by
      have ha : raw11850step2 = -raw11850step1 := by apply Matrix.ext; change ∀ i j, raw11850step2 i j = -(raw11850step1 i j); unfold raw11850step2 raw11850step1; decide +kernel
      have hl : raw11850step2Labels = raw11850step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11850step2 raw11850step2Labels = mixedMoment B raw11850step3 raw11850step3Labels := by
      have ha : raw11850step3 = raw11850step2 := by apply Matrix.ext; unfold raw11850step3 raw11850step2; decide +kernel
      have hl : raw11850step2Labels = labelEmbedding1 ∘ raw11850step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11850step2 raw11850step2Labels raw11850step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw11851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11851Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw11851step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11851step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11851step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11851 raw11851Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw11851 raw11851Labels = mixedMoment B raw11851step0 raw11851step0Labels := by
      have ha : raw11851step0 = (fun i j => raw11851 (permutation167 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11851step0 raw11851; decide +kernel
      have hl : raw11851step0Labels = raw11851Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11851 raw11851Labels permutation167 permutation7
    mixedMoment B raw11851step0 raw11851step0Labels = mixedMoment B raw11851step1 raw11851step1Labels := by
      have ha : raw11851step1 = -raw11851step0 := by apply Matrix.ext; change ∀ i j, raw11851step1 i j = -(raw11851step0 i j); unfold raw11851step1 raw11851step0; decide +kernel
      have hl : raw11851step1Labels = raw11851step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11851step1 raw11851step1Labels = mixedMoment B raw11851step2 raw11851step2Labels := by
      have ha : raw11851step2 = raw11851step1 := by apply Matrix.ext; unfold raw11851step2 raw11851step1; decide +kernel
      have hl : raw11851step1Labels = labelEmbedding1 ∘ raw11851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11851step1 raw11851step1Labels raw11851step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3528 node3528Labels := by rfl

def raw11852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11852step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11852step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11852step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11852 raw11852Labels = mixedMoment B node3238 node3238Labels := by
  calc
    mixedMoment B raw11852 raw11852Labels = mixedMoment B raw11852step0 raw11852step0Labels := by
      have ha : raw11852step0 = (fun i j => raw11852 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11852step0 raw11852; decide +kernel
      have hl : raw11852step0Labels = raw11852Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11852 raw11852Labels permutation194 permutation5
    mixedMoment B raw11852step0 raw11852step0Labels = mixedMoment B raw11852step1 raw11852step1Labels := by
      have ha : raw11852step1 = -raw11852step0 := by apply Matrix.ext; change ∀ i j, raw11852step1 i j = -(raw11852step0 i j); unfold raw11852step1 raw11852step0; decide +kernel
      have hl : raw11852step1Labels = raw11852step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11852step1 raw11852step1Labels = mixedMoment B raw11852step2 raw11852step2Labels := by
      have ha : raw11852step2 = raw11852step1 := by apply Matrix.ext; unfold raw11852step2 raw11852step1; decide +kernel
      have hl : raw11852step1Labels = labelEmbedding1 ∘ raw11852step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11852step1 raw11852step1Labels raw11852step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3238 node3238Labels := by rfl

def raw11853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw11853step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11853step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11853step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11853 raw11853Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw11853 raw11853Labels = mixedMoment B raw11853step0 raw11853step0Labels := by
      have ha : raw11853step0 = (fun i j => raw11853 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11853step0 raw11853; decide +kernel
      have hl : raw11853step0Labels = raw11853Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11853 raw11853Labels permutation161 permutation7
    mixedMoment B raw11853step0 raw11853step0Labels = mixedMoment B raw11853step1 raw11853step1Labels := by
      have ha : raw11853step1 = -raw11853step0 := by apply Matrix.ext; change ∀ i j, raw11853step1 i j = -(raw11853step0 i j); unfold raw11853step1 raw11853step0; decide +kernel
      have hl : raw11853step1Labels = raw11853step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11853step1 raw11853step1Labels = mixedMoment B raw11853step2 raw11853step2Labels := by
      have ha : raw11853step2 = raw11853step1 := by apply Matrix.ext; unfold raw11853step2 raw11853step1; decide +kernel
      have hl : raw11853step1Labels = labelEmbedding1 ∘ raw11853step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11853step1 raw11853step1Labels raw11853step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw11854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11854step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11854step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11854 raw11854Labels = mixedMoment B node2833 node2833Labels := by
  calc
    mixedMoment B raw11854 raw11854Labels = mixedMoment B raw11854step0 raw11854step0Labels := by
      have ha : raw11854step0 = (fun i j => raw11854 (permutation361 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11854step0 raw11854; decide +kernel
      have hl : raw11854step0Labels = raw11854Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11854 raw11854Labels permutation361 permutation5
    mixedMoment B raw11854step0 raw11854step0Labels = mixedMoment B raw11854step1 raw11854step1Labels := by
      have ha : raw11854step1 = -raw11854step0 := by apply Matrix.ext; change ∀ i j, raw11854step1 i j = -(raw11854step0 i j); unfold raw11854step1 raw11854step0; decide +kernel
      have hl : raw11854step1Labels = raw11854step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11854step1 raw11854step1Labels = mixedMoment B raw11854step2 raw11854step2Labels := by
      have ha : raw11854step2 = raw11854step1 := by apply Matrix.ext; unfold raw11854step2 raw11854step1; decide +kernel
      have hl : raw11854step1Labels = labelEmbedding1 ∘ raw11854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11854step1 raw11854step1Labels raw11854step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2833 node2833Labels := by rfl

def raw11855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw11855step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw11855step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11855step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11855step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11855step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11855 raw11855Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw11855 raw11855Labels = mixedMoment B raw11855step0 raw11855step0Labels := by
      have hz : ∀ j, raw11855 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11855step0 = (fun i j => raw11855 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11855step0 raw11855; decide +kernel
      have hl : raw11855step0Labels = raw11855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11855 raw11855Labels permutation434 hz
    mixedMoment B raw11855step0 raw11855step0Labels = mixedMoment B raw11855step1 raw11855step1Labels := by
      have ha : raw11855step1 = (fun i j => raw11855step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11855step1 raw11855step0; decide +kernel
      have hl : raw11855step1Labels = raw11855step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11855step0 raw11855step0Labels permutation35 permutation7
    mixedMoment B raw11855step1 raw11855step1Labels = mixedMoment B raw11855step2 raw11855step2Labels := by
      have ha : raw11855step2 = -raw11855step1 := by apply Matrix.ext; change ∀ i j, raw11855step2 i j = -(raw11855step1 i j); unfold raw11855step2 raw11855step1; decide +kernel
      have hl : raw11855step2Labels = raw11855step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11855step2 raw11855step2Labels = mixedMoment B raw11855step3 raw11855step3Labels := by
      have ha : raw11855step3 = raw11855step2 := by apply Matrix.ext; unfold raw11855step3 raw11855step2; decide +kernel
      have hl : raw11855step2Labels = labelEmbedding1 ∘ raw11855step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11855step2 raw11855step2Labels raw11855step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw11856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw11856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw11856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11856step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11856step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11856 raw11856Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw11856 raw11856Labels = mixedMoment B raw11856step0 raw11856step0Labels := by
      have ha : raw11856step0 = (fun i j => raw11856 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11856step0 raw11856; decide +kernel
      have hl : raw11856step0Labels = raw11856Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11856 raw11856Labels permutation161 permutation7
    mixedMoment B raw11856step0 raw11856step0Labels = mixedMoment B raw11856step1 raw11856step1Labels := by
      have ha : raw11856step1 = -raw11856step0 := by apply Matrix.ext; change ∀ i j, raw11856step1 i j = -(raw11856step0 i j); unfold raw11856step1 raw11856step0; decide +kernel
      have hl : raw11856step1Labels = raw11856step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11856step1 raw11856step1Labels = mixedMoment B raw11856step2 raw11856step2Labels := by
      have ha : raw11856step2 = raw11856step1 := by apply Matrix.ext; unfold raw11856step2 raw11856step1; decide +kernel
      have hl : raw11856step1Labels = labelEmbedding1 ∘ raw11856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11856step1 raw11856step1Labels raw11856step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3528 node3528Labels := by rfl

def raw11857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11857step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11857step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11857step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11857 raw11857Labels = mixedMoment B node3241 node3241Labels := by
  calc
    mixedMoment B raw11857 raw11857Labels = mixedMoment B raw11857step0 raw11857step0Labels := by
      have ha : raw11857step0 = (fun i j => raw11857 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11857step0 raw11857; decide +kernel
      have hl : raw11857step0Labels = raw11857Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11857 raw11857Labels permutation176 permutation5
    mixedMoment B raw11857step0 raw11857step0Labels = mixedMoment B raw11857step1 raw11857step1Labels := by
      have ha : raw11857step1 = -raw11857step0 := by apply Matrix.ext; change ∀ i j, raw11857step1 i j = -(raw11857step0 i j); unfold raw11857step1 raw11857step0; decide +kernel
      have hl : raw11857step1Labels = raw11857step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11857step1 raw11857step1Labels = mixedMoment B raw11857step2 raw11857step2Labels := by
      have ha : raw11857step2 = raw11857step1 := by apply Matrix.ext; unfold raw11857step2 raw11857step1; decide +kernel
      have hl : raw11857step1Labels = labelEmbedding1 ∘ raw11857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11857step1 raw11857step1Labels raw11857step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3241 node3241Labels := by rfl

def raw11858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11858step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11858step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11858 raw11858Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw11858 raw11858Labels = mixedMoment B raw11858step0 raw11858step0Labels := by
      have ha : raw11858step0 = (fun i j => raw11858 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11858step0 raw11858; decide +kernel
      have hl : raw11858step0Labels = raw11858Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11858 raw11858Labels permutation161 permutation7
    mixedMoment B raw11858step0 raw11858step0Labels = mixedMoment B raw11858step1 raw11858step1Labels := by
      have ha : raw11858step1 = -raw11858step0 := by apply Matrix.ext; change ∀ i j, raw11858step1 i j = -(raw11858step0 i j); unfold raw11858step1 raw11858step0; decide +kernel
      have hl : raw11858step1Labels = raw11858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11858step1 raw11858step1Labels = mixedMoment B raw11858step2 raw11858step2Labels := by
      have ha : raw11858step2 = raw11858step1 := by apply Matrix.ext; unfold raw11858step2 raw11858step1; decide +kernel
      have hl : raw11858step1Labels = labelEmbedding1 ∘ raw11858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11858step1 raw11858step1Labels raw11858step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw11859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11859step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11859step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11859 raw11859Labels = mixedMoment B node2836 node2836Labels := by
  calc
    mixedMoment B raw11859 raw11859Labels = mixedMoment B raw11859step0 raw11859step0Labels := by
      have ha : raw11859step0 = (fun i j => raw11859 (permutation346 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11859step0 raw11859; decide +kernel
      have hl : raw11859step0Labels = raw11859Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11859 raw11859Labels permutation346 permutation5
    mixedMoment B raw11859step0 raw11859step0Labels = mixedMoment B raw11859step1 raw11859step1Labels := by
      have ha : raw11859step1 = -raw11859step0 := by apply Matrix.ext; change ∀ i j, raw11859step1 i j = -(raw11859step0 i j); unfold raw11859step1 raw11859step0; decide +kernel
      have hl : raw11859step1Labels = raw11859step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11859step1 raw11859step1Labels = mixedMoment B raw11859step2 raw11859step2Labels := by
      have ha : raw11859step2 = raw11859step1 := by apply Matrix.ext; unfold raw11859step2 raw11859step1; decide +kernel
      have hl : raw11859step1Labels = labelEmbedding1 ∘ raw11859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11859step1 raw11859step1Labels raw11859step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2836 node2836Labels := by rfl

def raw11860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11860step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11860step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11860step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11860step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11860 raw11860Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw11860 raw11860Labels = mixedMoment B raw11860step0 raw11860step0Labels := by
      have hz : ∀ j, raw11860 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11860step0 = (fun i j => raw11860 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11860step0 raw11860; decide +kernel
      have hl : raw11860step0Labels = raw11860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11860 raw11860Labels permutation434 hz
    mixedMoment B raw11860step0 raw11860step0Labels = mixedMoment B raw11860step1 raw11860step1Labels := by
      have ha : raw11860step1 = (fun i j => raw11860step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11860step1 raw11860step0; decide +kernel
      have hl : raw11860step1Labels = raw11860step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11860step0 raw11860step0Labels permutation35 permutation7
    mixedMoment B raw11860step1 raw11860step1Labels = mixedMoment B raw11860step2 raw11860step2Labels := by
      have ha : raw11860step2 = -raw11860step1 := by apply Matrix.ext; change ∀ i j, raw11860step2 i j = -(raw11860step1 i j); unfold raw11860step2 raw11860step1; decide +kernel
      have hl : raw11860step2Labels = raw11860step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11860step2 raw11860step2Labels = mixedMoment B raw11860step3 raw11860step3Labels := by
      have ha : raw11860step3 = raw11860step2 := by apply Matrix.ext; unfold raw11860step3 raw11860step2; decide +kernel
      have hl : raw11860step2Labels = labelEmbedding1 ∘ raw11860step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11860step2 raw11860step2Labels raw11860step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw11861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11861step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11861step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11861step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11861 raw11861Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw11861 raw11861Labels = mixedMoment B raw11861step0 raw11861step0Labels := by
      have hz : ∀ j, raw11861 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11861step0 = (fun i j => raw11861 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11861step0 raw11861; decide +kernel
      have hl : raw11861step0Labels = raw11861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11861 raw11861Labels permutation520 hz
    mixedMoment B raw11861step0 raw11861step0Labels = mixedMoment B raw11861step1 raw11861step1Labels := by
      have ha : raw11861step1 = (fun i j => raw11861step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11861step1 raw11861step0; decide +kernel
      have hl : raw11861step1Labels = raw11861step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11861step0 raw11861step0Labels permutation35 permutation7
    mixedMoment B raw11861step1 raw11861step1Labels = mixedMoment B raw11861step2 raw11861step2Labels := by
      have ha : raw11861step2 = -raw11861step1 := by apply Matrix.ext; change ∀ i j, raw11861step2 i j = -(raw11861step1 i j); unfold raw11861step2 raw11861step1; decide +kernel
      have hl : raw11861step2Labels = raw11861step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11861step2 raw11861step2Labels = mixedMoment B raw11861step3 raw11861step3Labels := by
      have ha : raw11861step3 = raw11861step2 := by apply Matrix.ext; unfold raw11861step3 raw11861step2; decide +kernel
      have hl : raw11861step2Labels = labelEmbedding1 ∘ raw11861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11861step2 raw11861step2Labels raw11861step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw11862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11862 raw11862Labels = mixedMoment B node2730 node2730Labels := by
  calc
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw11863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11863 raw11863Labels = mixedMoment B node3812 node3812Labels := by
  calc
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw11864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11864 raw11864Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw11864 raw11864Labels = mixedMoment B raw11864step0 raw11864step0Labels := by
      have ha : raw11864step0 = (fun i j => raw11864 (permutation416 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11864step0 raw11864; decide +kernel
      have hl : raw11864step0Labels = raw11864Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11864 raw11864Labels permutation416 permutation4
    mixedMoment B raw11864step0 raw11864step0Labels = mixedMoment B raw11864step1 raw11864step1Labels := by
      have ha : raw11864step1 = -raw11864step0 := by apply Matrix.ext; change ∀ i j, raw11864step1 i j = -(raw11864step0 i j); unfold raw11864step1 raw11864step0; decide +kernel
      have hl : raw11864step1Labels = raw11864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw11865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11865 raw11865Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw11865 raw11865Labels = mixedMoment B raw11865step0 raw11865step0Labels := by
      have hz : ∀ j, raw11865 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11865step0 = (fun i j => raw11865 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11865step0 raw11865; decide +kernel
      have hl : raw11865step0Labels = raw11865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11865 raw11865Labels permutation434 hz
    _ = mixedMoment B node3906 node3906Labels := by rfl

def raw11866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11866 raw11866Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw11866 raw11866Labels = mixedMoment B raw11866step0 raw11866step0Labels := by
      have hz : ∀ j, raw11866 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11866step0 = (fun i j => raw11866 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11866step0 raw11866; decide +kernel
      have hl : raw11866step0Labels = raw11866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11866 raw11866Labels permutation520 hz
    _ = mixedMoment B node3906 node3906Labels := by rfl

def raw11867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11867 raw11867Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw11867 raw11867Labels = mixedMoment B raw11867step0 raw11867step0Labels := by
      have ha : raw11867step0 = (fun i j => raw11867 (permutation416 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11867step0 raw11867; decide +kernel
      have hl : raw11867step0Labels = raw11867Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11867 raw11867Labels permutation416 permutation4
    mixedMoment B raw11867step0 raw11867step0Labels = mixedMoment B raw11867step1 raw11867step1Labels := by
      have ha : raw11867step1 = -raw11867step0 := by apply Matrix.ext; change ∀ i j, raw11867step1 i j = -(raw11867step0 i j); unfold raw11867step1 raw11867step0; decide +kernel
      have hl : raw11867step1Labels = raw11867step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw11868 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]
def raw11868Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11868step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]
def raw11868step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11868step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw11868step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11868step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw11868step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11868 raw11868Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw11868 raw11868Labels = mixedMoment B raw11868step0 raw11868step0Labels := by
      have hz : ∀ j, raw11868 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11868step0 = (fun i j => raw11868 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11868step0 raw11868; decide +kernel
      have hl : raw11868step0Labels = raw11868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11868 raw11868Labels permutation520 hz
    mixedMoment B raw11868step0 raw11868step0Labels = mixedMoment B raw11868step1 raw11868step1Labels := by
      have hz : ∀ j, raw11868step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11868step1 = (fun i j => raw11868step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11868step1 raw11868step0; decide +kernel
      have hl : raw11868step1Labels = raw11868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11868step0 raw11868step0Labels permutation104 hz
    mixedMoment B raw11868step1 raw11868step1Labels = mixedMoment B raw11868step2 raw11868step2Labels := by
      have ha : raw11868step2 = (fun i j => raw11868step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11868step2 raw11868step1; decide +kernel
      have hl : raw11868step2Labels = raw11868step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11868step1 raw11868step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw11869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11869 raw11869Labels = mixedMoment B node1276 node1276Labels := by
  calc
    mixedMoment B raw11869 raw11869Labels = mixedMoment B raw11869step0 raw11869step0Labels := by
      have ha : raw11869step0 = (fun i j => raw11869 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11869step0 raw11869; decide +kernel
      have hl : raw11869step0Labels = raw11869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11869 raw11869Labels permutation176 permutation2
    _ = mixedMoment B node1276 node1276Labels := by rfl

def raw11870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11870 raw11870Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw11870 raw11870Labels = mixedMoment B raw11870step0 raw11870step0Labels := by
      have ha : raw11870step0 = (fun i j => raw11870 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11870step0 raw11870; decide +kernel
      have hl : raw11870step0Labels = raw11870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11870 raw11870Labels permutation161 permutation2
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw11871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11871 raw11871Labels = mixedMoment B node1223 node1223Labels := by
  calc
    mixedMoment B raw11871 raw11871Labels = mixedMoment B raw11871step0 raw11871step0Labels := by
      have ha : raw11871step0 = (fun i j => raw11871 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11871step0 raw11871; decide +kernel
      have hl : raw11871step0Labels = raw11871Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11871 raw11871Labels permutation155 permutation2
    _ = mixedMoment B node1223 node1223Labels := by rfl

def raw11872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11872 raw11872Labels = mixedMoment B node1223 node1223Labels := by
  calc
    mixedMoment B raw11872 raw11872Labels = mixedMoment B raw11872step0 raw11872step0Labels := by
      have ha : raw11872step0 = (fun i j => raw11872 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11872step0 raw11872; decide +kernel
      have hl : raw11872step0Labels = raw11872Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11872 raw11872Labels permutation153 permutation2
    _ = mixedMoment B node1223 node1223Labels := by rfl

def raw11873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11873 raw11873Labels = mixedMoment B node1222 node1222Labels := by
  calc
    _ = mixedMoment B node1222 node1222Labels := by rfl

def raw11874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw11874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11874 raw11874Labels = mixedMoment B node2645 node2645Labels := by
  calc
    mixedMoment B raw11874 raw11874Labels = mixedMoment B raw11874step0 raw11874step0Labels := by
      have ha : raw11874step0 = (fun i j => raw11874 (permutation364 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11874step0 raw11874; decide +kernel
      have hl : raw11874step0Labels = raw11874Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11874 raw11874Labels permutation364 permutation4
    mixedMoment B raw11874step0 raw11874step0Labels = mixedMoment B raw11874step1 raw11874step1Labels := by
      have ha : raw11874step1 = -raw11874step0 := by apply Matrix.ext; change ∀ i j, raw11874step1 i j = -(raw11874step0 i j); unfold raw11874step1 raw11874step0; decide +kernel
      have hl : raw11874step1Labels = raw11874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2645 node2645Labels := by rfl

def raw11875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11875 raw11875Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw11875 raw11875Labels = mixedMoment B raw11875step0 raw11875step0Labels := by
      have hz : ∀ j, raw11875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11875step0 = (fun i j => raw11875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11875step0 raw11875; decide +kernel
      have hl : raw11875step0Labels = raw11875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11875 raw11875Labels permutation434 hz
    mixedMoment B raw11875step0 raw11875step0Labels = mixedMoment B raw11875step1 raw11875step1Labels := by
      have ha : raw11875step1 = (fun i j => raw11875step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11875step1 raw11875step0; decide +kernel
      have hl : raw11875step1Labels = raw11875step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11875step0 raw11875step0Labels permutation38 permutation2
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw11876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11876 raw11876Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw11876 raw11876Labels = mixedMoment B raw11876step0 raw11876step0Labels := by
      have hz : ∀ j, raw11876 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11876step0 = (fun i j => raw11876 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11876step0 raw11876; decide +kernel
      have hl : raw11876step0Labels = raw11876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11876 raw11876Labels permutation520 hz
    mixedMoment B raw11876step0 raw11876step0Labels = mixedMoment B raw11876step1 raw11876step1Labels := by
      have ha : raw11876step1 = (fun i j => raw11876step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11876step1 raw11876step0; decide +kernel
      have hl : raw11876step1Labels = raw11876step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11876step0 raw11876step0Labels permutation38 permutation2
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw11877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw11877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw11877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11877 raw11877Labels = mixedMoment B node2757 node2757Labels := by
  calc
    mixedMoment B raw11877 raw11877Labels = mixedMoment B raw11877step0 raw11877step0Labels := by
      have ha : raw11877step0 = (fun i j => raw11877 (permutation252 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11877step0 raw11877; decide +kernel
      have hl : raw11877step0Labels = raw11877Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11877 raw11877Labels permutation252 permutation2
    _ = mixedMoment B node2757 node2757Labels := by rfl

def raw11878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11878 raw11878Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw11878 raw11878Labels = mixedMoment B raw11878step0 raw11878step0Labels := by
      have ha : raw11878step0 = (fun i j => raw11878 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11878step0 raw11878; decide +kernel
      have hl : raw11878step0Labels = raw11878Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11878 raw11878Labels permutation161 permutation2
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw11879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11879 raw11879Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw11879 raw11879Labels = mixedMoment B raw11879step0 raw11879step0Labels := by
      have ha : raw11879step0 = (fun i j => raw11879 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11879step0 raw11879; decide +kernel
      have hl : raw11879step0Labels = raw11879Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11879 raw11879Labels permutation155 permutation2
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw11880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11880 raw11880Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw11880 raw11880Labels = mixedMoment B raw11880step0 raw11880step0Labels := by
      have ha : raw11880step0 = (fun i j => raw11880 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11880step0 raw11880; decide +kernel
      have hl : raw11880step0Labels = raw11880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11880 raw11880Labels permutation153 permutation2
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw11881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11881 raw11881Labels = mixedMoment B node2493 node2493Labels := by
  calc
    _ = mixedMoment B node2493 node2493Labels := by rfl

def raw11882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11882step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11882 raw11882Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw11882 raw11882Labels = mixedMoment B raw11882step0 raw11882step0Labels := by
      have ha : raw11882step0 = (fun i j => raw11882 (permutation426 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11882step0 raw11882; decide +kernel
      have hl : raw11882step0Labels = raw11882Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11882 raw11882Labels permutation426 permutation4
    mixedMoment B raw11882step0 raw11882step0Labels = mixedMoment B raw11882step1 raw11882step1Labels := by
      have ha : raw11882step1 = raw11882step0 := by apply Matrix.ext; unfold raw11882step1 raw11882step0; decide +kernel
      have hl : raw11882step0Labels = labelEmbedding7 ∘ raw11882step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11882step0 raw11882step0Labels raw11882step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw11883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11883 raw11883Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw11883 raw11883Labels = mixedMoment B raw11883step0 raw11883step0Labels := by
      have ha : raw11883step0 = (fun i j => raw11883 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11883step0 raw11883; decide +kernel
      have hl : raw11883step0Labels = raw11883Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11883 raw11883Labels permutation180 permutation2
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw11884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11884step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11884 raw11884Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw11884 raw11884Labels = mixedMoment B raw11884step0 raw11884step0Labels := by
      have ha : raw11884step0 = (fun i j => raw11884 (permutation428 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11884step0 raw11884; decide +kernel
      have hl : raw11884step0Labels = raw11884Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11884 raw11884Labels permutation428 permutation4
    mixedMoment B raw11884step0 raw11884step0Labels = mixedMoment B raw11884step1 raw11884step1Labels := by
      have ha : raw11884step1 = raw11884step0 := by apply Matrix.ext; unfold raw11884step1 raw11884step0; decide +kernel
      have hl : raw11884step0Labels = labelEmbedding7 ∘ raw11884step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11884step0 raw11884step0Labels raw11884step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw11885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11885step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11885 raw11885Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw11885 raw11885Labels = mixedMoment B raw11885step0 raw11885step0Labels := by
      have ha : raw11885step0 = (fun i j => raw11885 (permutation424 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11885step0 raw11885; decide +kernel
      have hl : raw11885step0Labels = raw11885Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11885 raw11885Labels permutation424 permutation4
    mixedMoment B raw11885step0 raw11885step0Labels = mixedMoment B raw11885step1 raw11885step1Labels := by
      have ha : raw11885step1 = raw11885step0 := by apply Matrix.ext; unfold raw11885step1 raw11885step0; decide +kernel
      have hl : raw11885step0Labels = labelEmbedding7 ∘ raw11885step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11885step0 raw11885step0Labels raw11885step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw11886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11886step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11886step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11886step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11886step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11886step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11886 raw11886Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw11886 raw11886Labels = mixedMoment B raw11886step0 raw11886step0Labels := by
      have hz : ∀ j, raw11886 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11886step0 = (fun i j => raw11886 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11886step0 raw11886; decide +kernel
      have hl : raw11886step0Labels = raw11886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11886 raw11886Labels permutation590 hz
    mixedMoment B raw11886step0 raw11886step0Labels = mixedMoment B raw11886step1 raw11886step1Labels := by
      have ha : raw11886step1 = (fun i j => raw11886step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11886step1 raw11886step0; decide +kernel
      have hl : raw11886step1Labels = raw11886step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11886step0 raw11886step0Labels permutation83 permutation6
    mixedMoment B raw11886step1 raw11886step1Labels = mixedMoment B raw11886step2 raw11886step2Labels := by
      have ha : raw11886step2 = -raw11886step1 := by apply Matrix.ext; change ∀ i j, raw11886step2 i j = -(raw11886step1 i j); unfold raw11886step2 raw11886step1; decide +kernel
      have hl : raw11886step2Labels = raw11886step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11886step2 raw11886step2Labels = mixedMoment B raw11886step3 raw11886step3Labels := by
      have ha : raw11886step3 = raw11886step2 := by apply Matrix.ext; unfold raw11886step3 raw11886step2; decide +kernel
      have hl : raw11886step2Labels = labelEmbedding9 ∘ raw11886step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11886step2 raw11886step2Labels raw11886step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw11887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11887step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11887 raw11887Labels = mixedMoment B node4473 node4473Labels := by
  calc
    mixedMoment B raw11887 raw11887Labels = mixedMoment B raw11887step0 raw11887step0Labels := by
      have ha : raw11887step0 = (fun i j => raw11887 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11887step0 raw11887; decide +kernel
      have hl : raw11887step0Labels = raw11887Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11887 raw11887Labels permutation176 permutation3
    mixedMoment B raw11887step0 raw11887step0Labels = mixedMoment B raw11887step1 raw11887step1Labels := by
      have ha : raw11887step1 = raw11887step0 := by apply Matrix.ext; unfold raw11887step1 raw11887step0; decide +kernel
      have hl : raw11887step0Labels = labelEmbedding6 ∘ raw11887step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11887step0 raw11887step0Labels raw11887step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4473 node4473Labels := by rfl

def raw11888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11888step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11888 raw11888Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw11888 raw11888Labels = mixedMoment B raw11888step0 raw11888step0Labels := by
      have ha : raw11888step0 = (fun i j => raw11888 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11888step0 raw11888; decide +kernel
      have hl : raw11888step0Labels = raw11888Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11888 raw11888Labels permutation176 permutation3
    mixedMoment B raw11888step0 raw11888step0Labels = mixedMoment B raw11888step1 raw11888step1Labels := by
      have ha : raw11888step1 = raw11888step0 := by apply Matrix.ext; unfold raw11888step1 raw11888step0; decide +kernel
      have hl : raw11888step0Labels = labelEmbedding6 ∘ raw11888step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11888step0 raw11888step0Labels raw11888step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw11889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11889step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11889 raw11889Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw11889 raw11889Labels = mixedMoment B raw11889step0 raw11889step0Labels := by
      have ha : raw11889step0 = (fun i j => raw11889 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11889step0 raw11889; decide +kernel
      have hl : raw11889step0Labels = raw11889Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11889 raw11889Labels permutation206 permutation3
    mixedMoment B raw11889step0 raw11889step0Labels = mixedMoment B raw11889step1 raw11889step1Labels := by
      have ha : raw11889step1 = raw11889step0 := by apply Matrix.ext; unfold raw11889step1 raw11889step0; decide +kernel
      have hl : raw11889step0Labels = labelEmbedding6 ∘ raw11889step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11889step0 raw11889step0Labels raw11889step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw11890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11890step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11890 raw11890Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw11890 raw11890Labels = mixedMoment B raw11890step0 raw11890step0Labels := by
      have ha : raw11890step0 = (fun i j => raw11890 (permutation230 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11890step0 raw11890; decide +kernel
      have hl : raw11890step0Labels = raw11890Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11890 raw11890Labels permutation230 permutation3
    mixedMoment B raw11890step0 raw11890step0Labels = mixedMoment B raw11890step1 raw11890step1Labels := by
      have ha : raw11890step1 = raw11890step0 := by apply Matrix.ext; unfold raw11890step1 raw11890step0; decide +kernel
      have hl : raw11890step0Labels = labelEmbedding6 ∘ raw11890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11890step0 raw11890step0Labels raw11890step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw11891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11891step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11891 raw11891Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw11891 raw11891Labels = mixedMoment B raw11891step0 raw11891step0Labels := by
      have hz : ∀ j, raw11891 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11891step0 = (fun i j => raw11891 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11891step0 raw11891; decide +kernel
      have hl : raw11891step0Labels = raw11891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11891 raw11891Labels permutation590 hz
    mixedMoment B raw11891step0 raw11891step0Labels = mixedMoment B raw11891step1 raw11891step1Labels := by
      have ha : raw11891step1 = (fun i j => raw11891step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11891step1 raw11891step0; decide +kernel
      have hl : raw11891step1Labels = raw11891step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11891step0 raw11891step0Labels permutation38 permutation3
    mixedMoment B raw11891step1 raw11891step1Labels = mixedMoment B raw11891step2 raw11891step2Labels := by
      have ha : raw11891step2 = raw11891step1 := by apply Matrix.ext; unfold raw11891step2 raw11891step1; decide +kernel
      have hl : raw11891step1Labels = labelEmbedding6 ∘ raw11891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11891step1 raw11891step1Labels raw11891step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw11892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11892step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11892 raw11892Labels = mixedMoment B node4414 node4414Labels := by
  calc
    mixedMoment B raw11892 raw11892Labels = mixedMoment B raw11892step0 raw11892step0Labels := by
      have ha : raw11892step0 = (fun i j => raw11892 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11892step0 raw11892; decide +kernel
      have hl : raw11892step0Labels = raw11892Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11892 raw11892Labels permutation161 permutation3
    mixedMoment B raw11892step0 raw11892step0Labels = mixedMoment B raw11892step1 raw11892step1Labels := by
      have ha : raw11892step1 = raw11892step0 := by apply Matrix.ext; unfold raw11892step1 raw11892step0; decide +kernel
      have hl : raw11892step0Labels = labelEmbedding6 ∘ raw11892step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11892step0 raw11892step0Labels raw11892step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4414 node4414Labels := by rfl

def raw11893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11893step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11893step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11893 raw11893Labels = mixedMoment B node5011 node5011Labels := by
  calc
    mixedMoment B raw11893 raw11893Labels = mixedMoment B raw11893step0 raw11893step0Labels := by
      have ha : raw11893step0 = (fun i j => raw11893 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11893step0 raw11893; decide +kernel
      have hl : raw11893step0Labels = raw11893Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11893 raw11893Labels permutation161 permutation3
    mixedMoment B raw11893step0 raw11893step0Labels = mixedMoment B raw11893step1 raw11893step1Labels := by
      have ha : raw11893step1 = raw11893step0 := by apply Matrix.ext; unfold raw11893step1 raw11893step0; decide +kernel
      have hl : raw11893step0Labels = labelEmbedding6 ∘ raw11893step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11893step0 raw11893step0Labels raw11893step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5011 node5011Labels := by rfl

def raw11894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11894step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11894 raw11894Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw11894 raw11894Labels = mixedMoment B raw11894step0 raw11894step0Labels := by
      have ha : raw11894step0 = (fun i j => raw11894 (permutation431 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11894step0 raw11894; decide +kernel
      have hl : raw11894step0Labels = raw11894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11894 raw11894Labels permutation431 permutation4
    mixedMoment B raw11894step0 raw11894step0Labels = mixedMoment B raw11894step1 raw11894step1Labels := by
      have ha : raw11894step1 = raw11894step0 := by apply Matrix.ext; unfold raw11894step1 raw11894step0; decide +kernel
      have hl : raw11894step0Labels = labelEmbedding7 ∘ raw11894step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11894step0 raw11894step0Labels raw11894step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw11895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11895step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11895 raw11895Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw11895 raw11895Labels = mixedMoment B raw11895step0 raw11895step0Labels := by
      have ha : raw11895step0 = (fun i j => raw11895 (permutation425 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11895step0 raw11895; decide +kernel
      have hl : raw11895step0Labels = raw11895Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11895 raw11895Labels permutation425 permutation4
    mixedMoment B raw11895step0 raw11895step0Labels = mixedMoment B raw11895step1 raw11895step1Labels := by
      have ha : raw11895step1 = raw11895step0 := by apply Matrix.ext; unfold raw11895step1 raw11895step0; decide +kernel
      have hl : raw11895step0Labels = labelEmbedding7 ∘ raw11895step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11895step0 raw11895step0Labels raw11895step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw11896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11896step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11896step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11896 raw11896Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw11896 raw11896Labels = mixedMoment B raw11896step0 raw11896step0Labels := by
      have hz : ∀ j, raw11896 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11896step0 = (fun i j => raw11896 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11896step0 raw11896; decide +kernel
      have hl : raw11896step0Labels = raw11896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11896 raw11896Labels permutation590 hz
    mixedMoment B raw11896step0 raw11896step0Labels = mixedMoment B raw11896step1 raw11896step1Labels := by
      have ha : raw11896step1 = (fun i j => raw11896step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11896step1 raw11896step0; decide +kernel
      have hl : raw11896step1Labels = raw11896step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11896step0 raw11896step0Labels permutation35 permutation3
    mixedMoment B raw11896step1 raw11896step1Labels = mixedMoment B raw11896step2 raw11896step2Labels := by
      have ha : raw11896step2 = raw11896step1 := by apply Matrix.ext; unfold raw11896step2 raw11896step1; decide +kernel
      have hl : raw11896step1Labels = labelEmbedding6 ∘ raw11896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11896step1 raw11896step1Labels raw11896step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw11897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11897step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11897 raw11897Labels = mixedMoment B node4407 node4407Labels := by
  calc
    mixedMoment B raw11897 raw11897Labels = mixedMoment B raw11897step0 raw11897step0Labels := by
      have ha : raw11897step0 = (fun i j => raw11897 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11897step0 raw11897; decide +kernel
      have hl : raw11897step0Labels = raw11897Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11897 raw11897Labels permutation155 permutation3
    mixedMoment B raw11897step0 raw11897step0Labels = mixedMoment B raw11897step1 raw11897step1Labels := by
      have ha : raw11897step1 = raw11897step0 := by apply Matrix.ext; unfold raw11897step1 raw11897step0; decide +kernel
      have hl : raw11897step0Labels = labelEmbedding6 ∘ raw11897step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11897step0 raw11897step0Labels raw11897step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4407 node4407Labels := by rfl

def raw11898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11898step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11898step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11898 raw11898Labels = mixedMoment B node5005 node5005Labels := by
  calc
    mixedMoment B raw11898 raw11898Labels = mixedMoment B raw11898step0 raw11898step0Labels := by
      have ha : raw11898step0 = (fun i j => raw11898 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11898step0 raw11898; decide +kernel
      have hl : raw11898step0Labels = raw11898Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11898 raw11898Labels permutation155 permutation3
    mixedMoment B raw11898step0 raw11898step0Labels = mixedMoment B raw11898step1 raw11898step1Labels := by
      have ha : raw11898step1 = raw11898step0 := by apply Matrix.ext; unfold raw11898step1 raw11898step0; decide +kernel
      have hl : raw11898step0Labels = labelEmbedding6 ∘ raw11898step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11898step0 raw11898step0Labels raw11898step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5005 node5005Labels := by rfl

def raw11899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11899step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11899 raw11899Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw11899 raw11899Labels = mixedMoment B raw11899step0 raw11899step0Labels := by
      have ha : raw11899step0 = (fun i j => raw11899 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11899step0 raw11899; decide +kernel
      have hl : raw11899step0Labels = raw11899Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11899 raw11899Labels permutation179 permutation3
    mixedMoment B raw11899step0 raw11899step0Labels = mixedMoment B raw11899step1 raw11899step1Labels := by
      have ha : raw11899step1 = raw11899step0 := by apply Matrix.ext; unfold raw11899step1 raw11899step0; decide +kernel
      have hl : raw11899step0Labels = labelEmbedding6 ∘ raw11899step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11899step0 raw11899step0Labels raw11899step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw11900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw11900step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw11900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11900 raw11900Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw11900 raw11900Labels = mixedMoment B raw11900step0 raw11900step0Labels := by
      have ha : raw11900step0 = (fun i j => raw11900 (permutation165 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11900step0 raw11900; decide +kernel
      have hl : raw11900step0Labels = raw11900Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11900 raw11900Labels permutation165 permutation3
    mixedMoment B raw11900step0 raw11900step0Labels = mixedMoment B raw11900step1 raw11900step1Labels := by
      have ha : raw11900step1 = raw11900step0 := by apply Matrix.ext; unfold raw11900step1 raw11900step0; decide +kernel
      have hl : raw11900step0Labels = labelEmbedding6 ∘ raw11900step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11900step0 raw11900step0Labels raw11900step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

def raw11901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw11901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11901step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11901 raw11901Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw11901 raw11901Labels = mixedMoment B raw11901step0 raw11901step0Labels := by
      have hz : ∀ j, raw11901 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11901step0 = (fun i j => raw11901 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11901step0 raw11901; decide +kernel
      have hl : raw11901step0Labels = raw11901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11901 raw11901Labels permutation590 hz
    mixedMoment B raw11901step0 raw11901step0Labels = mixedMoment B raw11901step1 raw11901step1Labels := by
      have ha : raw11901step1 = (fun i j => raw11901step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11901step1 raw11901step0; decide +kernel
      have hl : raw11901step1Labels = raw11901step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11901step0 raw11901step0Labels permutation33 permutation3
    mixedMoment B raw11901step1 raw11901step1Labels = mixedMoment B raw11901step2 raw11901step2Labels := by
      have ha : raw11901step2 = raw11901step1 := by apply Matrix.ext; unfold raw11901step2 raw11901step1; decide +kernel
      have hl : raw11901step1Labels = labelEmbedding6 ∘ raw11901step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11901step1 raw11901step1Labels raw11901step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw11902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11902step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11902 raw11902Labels = mixedMoment B node4407 node4407Labels := by
  calc
    mixedMoment B raw11902 raw11902Labels = mixedMoment B raw11902step0 raw11902step0Labels := by
      have ha : raw11902step0 = (fun i j => raw11902 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11902step0 raw11902; decide +kernel
      have hl : raw11902step0Labels = raw11902Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11902 raw11902Labels permutation153 permutation3
    mixedMoment B raw11902step0 raw11902step0Labels = mixedMoment B raw11902step1 raw11902step1Labels := by
      have ha : raw11902step1 = raw11902step0 := by apply Matrix.ext; unfold raw11902step1 raw11902step0; decide +kernel
      have hl : raw11902step0Labels = labelEmbedding6 ∘ raw11902step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11902step0 raw11902step0Labels raw11902step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4407 node4407Labels := by rfl

def raw11903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11903step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11903 raw11903Labels = mixedMoment B node5005 node5005Labels := by
  calc
    mixedMoment B raw11903 raw11903Labels = mixedMoment B raw11903step0 raw11903step0Labels := by
      have ha : raw11903step0 = (fun i j => raw11903 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11903step0 raw11903; decide +kernel
      have hl : raw11903step0Labels = raw11903Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11903 raw11903Labels permutation153 permutation3
    mixedMoment B raw11903step0 raw11903step0Labels = mixedMoment B raw11903step1 raw11903step1Labels := by
      have ha : raw11903step1 = raw11903step0 := by apply Matrix.ext; unfold raw11903step1 raw11903step0; decide +kernel
      have hl : raw11903step0Labels = labelEmbedding6 ∘ raw11903step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11903step0 raw11903step0Labels raw11903step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5005 node5005Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
