import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18816step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18816step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18816 raw18816Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18816 raw18816Labels = mixedMoment B raw18816step0 raw18816step0Labels := by
      have hz : ∀ j, raw18816 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18816step0 = (fun i j => raw18816 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18816step0 raw18816; decide +kernel
      have hl : raw18816step0Labels = raw18816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18816 raw18816Labels permutation520 hz
    mixedMoment B raw18816step0 raw18816step0Labels = mixedMoment B raw18816step1 raw18816step1Labels := by
      have ha : raw18816step1 = (fun i j => raw18816step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18816step1 raw18816step0; decide +kernel
      have hl : raw18816step1Labels = raw18816step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18816step0 raw18816step0Labels permutation37 permutation3
    mixedMoment B raw18816step1 raw18816step1Labels = mixedMoment B raw18816step2 raw18816step2Labels := by
      have ha : raw18816step2 = raw18816step1 := by apply Matrix.ext; unfold raw18816step2 raw18816step1; decide +kernel
      have hl : raw18816step1Labels = labelEmbedding6 ∘ raw18816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18816step1 raw18816step1Labels raw18816step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw18817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18817step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18817step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18817step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18817step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18817 raw18817Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18817 raw18817Labels = mixedMoment B raw18817step0 raw18817step0Labels := by
      have ha : raw18817step0 = (fun i j => raw18817 (permutation605 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18817step0 raw18817; decide +kernel
      have hl : raw18817step0Labels = raw18817Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18817 raw18817Labels permutation605 permutation4
    mixedMoment B raw18817step0 raw18817step0Labels = mixedMoment B raw18817step1 raw18817step1Labels := by
      have ha : raw18817step1 = -raw18817step0 := by apply Matrix.ext; change ∀ i j, raw18817step1 i j = -(raw18817step0 i j); unfold raw18817step1 raw18817step0; decide +kernel
      have hl : raw18817step1Labels = raw18817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18817step1 raw18817step1Labels = mixedMoment B raw18817step2 raw18817step2Labels := by
      have ha : raw18817step2 = raw18817step1 := by apply Matrix.ext; unfold raw18817step2 raw18817step1; decide +kernel
      have hl : raw18817step1Labels = labelEmbedding7 ∘ raw18817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18817step1 raw18817step1Labels raw18817step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw18818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18818step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18818 raw18818Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw18818 raw18818Labels = mixedMoment B raw18818step0 raw18818step0Labels := by
      have ha : raw18818step0 = (fun i j => raw18818 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18818step0 raw18818; decide +kernel
      have hl : raw18818step0Labels = raw18818Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18818 raw18818Labels permutation157 permutation3
    mixedMoment B raw18818step0 raw18818step0Labels = mixedMoment B raw18818step1 raw18818step1Labels := by
      have ha : raw18818step1 = raw18818step0 := by apply Matrix.ext; unfold raw18818step1 raw18818step0; decide +kernel
      have hl : raw18818step0Labels = labelEmbedding6 ∘ raw18818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18818step0 raw18818step0Labels raw18818step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw18819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18819step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18819 raw18819Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw18819 raw18819Labels = mixedMoment B raw18819step0 raw18819step0Labels := by
      have ha : raw18819step0 = (fun i j => raw18819 (permutation270 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18819step0 raw18819; decide +kernel
      have hl : raw18819step0Labels = raw18819Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18819 raw18819Labels permutation270 permutation3
    mixedMoment B raw18819step0 raw18819step0Labels = mixedMoment B raw18819step1 raw18819step1Labels := by
      have ha : raw18819step1 = raw18819step0 := by apply Matrix.ext; unfold raw18819step1 raw18819step0; decide +kernel
      have hl : raw18819step0Labels = labelEmbedding6 ∘ raw18819step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18819step0 raw18819step0Labels raw18819step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw18820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18820step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18820step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18820step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18820 raw18820Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18820 raw18820Labels = mixedMoment B raw18820step0 raw18820step0Labels := by
      have ha : raw18820step0 = (fun i j => raw18820 (permutation504 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18820step0 raw18820; decide +kernel
      have hl : raw18820step0Labels = raw18820Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18820 raw18820Labels permutation504 permutation3
    mixedMoment B raw18820step0 raw18820step0Labels = mixedMoment B raw18820step1 raw18820step1Labels := by
      have ha : raw18820step1 = -raw18820step0 := by apply Matrix.ext; change ∀ i j, raw18820step1 i j = -(raw18820step0 i j); unfold raw18820step1 raw18820step0; decide +kernel
      have hl : raw18820step1Labels = raw18820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18820step1 raw18820step1Labels = mixedMoment B raw18820step2 raw18820step2Labels := by
      have ha : raw18820step2 = raw18820step1 := by apply Matrix.ext; unfold raw18820step2 raw18820step1; decide +kernel
      have hl : raw18820step1Labels = labelEmbedding6 ∘ raw18820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18820step1 raw18820step1Labels raw18820step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw18821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18821step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18821 raw18821Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18821 raw18821Labels = mixedMoment B raw18821step0 raw18821step0Labels := by
      have hz : ∀ j, raw18821 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18821step0 = (fun i j => raw18821 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18821step0 raw18821; decide +kernel
      have hl : raw18821step0Labels = raw18821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18821 raw18821Labels permutation520 hz
    mixedMoment B raw18821step0 raw18821step0Labels = mixedMoment B raw18821step1 raw18821step1Labels := by
      have ha : raw18821step1 = (fun i j => raw18821step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18821step1 raw18821step0; decide +kernel
      have hl : raw18821step1Labels = raw18821step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18821step0 raw18821step0Labels permutation121 permutation5
    mixedMoment B raw18821step1 raw18821step1Labels = mixedMoment B raw18821step2 raw18821step2Labels := by
      have ha : raw18821step2 = raw18821step1 := by apply Matrix.ext; unfold raw18821step2 raw18821step1; decide +kernel
      have hl : raw18821step1Labels = labelEmbedding8 ∘ raw18821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18821step1 raw18821step1Labels raw18821step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw18822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18822step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18822 raw18822Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw18822 raw18822Labels = mixedMoment B raw18822step0 raw18822step0Labels := by
      have ha : raw18822step0 = (fun i j => raw18822 (permutation496 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18822step0 raw18822; decide +kernel
      have hl : raw18822step0Labels = raw18822Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18822 raw18822Labels permutation496 permutation5
    mixedMoment B raw18822step0 raw18822step0Labels = mixedMoment B raw18822step1 raw18822step1Labels := by
      have ha : raw18822step1 = raw18822step0 := by apply Matrix.ext; unfold raw18822step1 raw18822step0; decide +kernel
      have hl : raw18822step0Labels = labelEmbedding8 ∘ raw18822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18822step0 raw18822step0Labels raw18822step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw18823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18823step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18823 raw18823Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw18823 raw18823Labels = mixedMoment B raw18823step0 raw18823step0Labels := by
      have ha : raw18823step0 = (fun i j => raw18823 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18823step0 raw18823; decide +kernel
      have hl : raw18823step0Labels = raw18823Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18823 raw18823Labels permutation156 permutation3
    mixedMoment B raw18823step0 raw18823step0Labels = mixedMoment B raw18823step1 raw18823step1Labels := by
      have ha : raw18823step1 = raw18823step0 := by apply Matrix.ext; unfold raw18823step1 raw18823step0; decide +kernel
      have hl : raw18823step0Labels = labelEmbedding6 ∘ raw18823step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18823step0 raw18823step0Labels raw18823step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw18824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18824step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18824 raw18824Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw18824 raw18824Labels = mixedMoment B raw18824step0 raw18824step0Labels := by
      have ha : raw18824step0 = (fun i j => raw18824 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18824step0 raw18824; decide +kernel
      have hl : raw18824step0Labels = raw18824Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18824 raw18824Labels permutation269 permutation3
    mixedMoment B raw18824step0 raw18824step0Labels = mixedMoment B raw18824step1 raw18824step1Labels := by
      have ha : raw18824step1 = raw18824step0 := by apply Matrix.ext; unfold raw18824step1 raw18824step0; decide +kernel
      have hl : raw18824step0Labels = labelEmbedding6 ∘ raw18824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18824step0 raw18824step0Labels raw18824step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw18825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18825step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18825step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18825step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18825 raw18825Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18825 raw18825Labels = mixedMoment B raw18825step0 raw18825step0Labels := by
      have ha : raw18825step0 = (fun i j => raw18825 (permutation568 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18825step0 raw18825; decide +kernel
      have hl : raw18825step0Labels = raw18825Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18825 raw18825Labels permutation568 permutation3
    mixedMoment B raw18825step0 raw18825step0Labels = mixedMoment B raw18825step1 raw18825step1Labels := by
      have ha : raw18825step1 = -raw18825step0 := by apply Matrix.ext; change ∀ i j, raw18825step1 i j = -(raw18825step0 i j); unfold raw18825step1 raw18825step0; decide +kernel
      have hl : raw18825step1Labels = raw18825step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18825step1 raw18825step1Labels = mixedMoment B raw18825step2 raw18825step2Labels := by
      have ha : raw18825step2 = raw18825step1 := by apply Matrix.ext; unfold raw18825step2 raw18825step1; decide +kernel
      have hl : raw18825step1Labels = labelEmbedding6 ∘ raw18825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18825step1 raw18825step1Labels raw18825step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw18826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18826step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18826step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18826 raw18826Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18826 raw18826Labels = mixedMoment B raw18826step0 raw18826step0Labels := by
      have hz : ∀ j, raw18826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18826step0 = (fun i j => raw18826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18826step0 raw18826; decide +kernel
      have hl : raw18826step0Labels = raw18826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18826 raw18826Labels permutation434 hz
    mixedMoment B raw18826step0 raw18826step0Labels = mixedMoment B raw18826step1 raw18826step1Labels := by
      have ha : raw18826step1 = (fun i j => raw18826step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18826step1 raw18826step0; decide +kernel
      have hl : raw18826step1Labels = raw18826step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18826step0 raw18826step0Labels permutation121 permutation5
    mixedMoment B raw18826step1 raw18826step1Labels = mixedMoment B raw18826step2 raw18826step2Labels := by
      have ha : raw18826step2 = raw18826step1 := by apply Matrix.ext; unfold raw18826step2 raw18826step1; decide +kernel
      have hl : raw18826step1Labels = labelEmbedding8 ∘ raw18826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18826step1 raw18826step1Labels raw18826step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw18827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18827step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18827 raw18827Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw18827 raw18827Labels = mixedMoment B raw18827step0 raw18827step0Labels := by
      have ha : raw18827step0 = (fun i j => raw18827 (permutation560 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18827step0 raw18827; decide +kernel
      have hl : raw18827step0Labels = raw18827Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18827 raw18827Labels permutation560 permutation5
    mixedMoment B raw18827step0 raw18827step0Labels = mixedMoment B raw18827step1 raw18827step1Labels := by
      have ha : raw18827step1 = raw18827step0 := by apply Matrix.ext; unfold raw18827step1 raw18827step0; decide +kernel
      have hl : raw18827step0Labels = labelEmbedding8 ∘ raw18827step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18827step0 raw18827step0Labels raw18827step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw18828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18828step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18828 raw18828Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw18828 raw18828Labels = mixedMoment B raw18828step0 raw18828step0Labels := by
      have ha : raw18828step0 = (fun i j => raw18828 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18828step0 raw18828; decide +kernel
      have hl : raw18828step0Labels = raw18828Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18828 raw18828Labels permutation152 permutation3
    mixedMoment B raw18828step0 raw18828step0Labels = mixedMoment B raw18828step1 raw18828step1Labels := by
      have ha : raw18828step1 = raw18828step0 := by apply Matrix.ext; unfold raw18828step1 raw18828step0; decide +kernel
      have hl : raw18828step0Labels = labelEmbedding6 ∘ raw18828step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18828step0 raw18828step0Labels raw18828step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw18829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18829step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18829 raw18829Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw18829 raw18829Labels = mixedMoment B raw18829step0 raw18829step0Labels := by
      have ha : raw18829step0 = (fun i j => raw18829 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18829step0 raw18829; decide +kernel
      have hl : raw18829step0Labels = raw18829Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18829 raw18829Labels permutation265 permutation3
    mixedMoment B raw18829step0 raw18829step0Labels = mixedMoment B raw18829step1 raw18829step1Labels := by
      have ha : raw18829step1 = raw18829step0 := by apply Matrix.ext; unfold raw18829step1 raw18829step0; decide +kernel
      have hl : raw18829step0Labels = labelEmbedding6 ∘ raw18829step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18829step0 raw18829step0Labels raw18829step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw18830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18830 raw18830Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw18830 raw18830Labels = mixedMoment B raw18830step0 raw18830step0Labels := by
      have ha : raw18830step0 = (fun i j => raw18830 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18830step0 raw18830; decide +kernel
      have hl : raw18830step0Labels = raw18830Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18830 raw18830Labels permutation662 permutation2
    mixedMoment B raw18830step0 raw18830step0Labels = mixedMoment B raw18830step1 raw18830step1Labels := by
      have ha : raw18830step1 = -raw18830step0 := by apply Matrix.ext; change ∀ i j, raw18830step1 i j = -(raw18830step0 i j); unfold raw18830step1 raw18830step0; decide +kernel
      have hl : raw18830step1Labels = raw18830step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw18831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18831step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18831 raw18831Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18831 raw18831Labels = mixedMoment B raw18831step0 raw18831step0Labels := by
      have hz : ∀ j, raw18831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18831step0 = (fun i j => raw18831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18831step0 raw18831; decide +kernel
      have hl : raw18831step0Labels = raw18831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18831 raw18831Labels permutation434 hz
    mixedMoment B raw18831step0 raw18831step0Labels = mixedMoment B raw18831step1 raw18831step1Labels := by
      have ha : raw18831step1 = (fun i j => raw18831step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18831step1 raw18831step0; decide +kernel
      have hl : raw18831step1Labels = raw18831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18831step0 raw18831step0Labels permutation151 permutation2
    mixedMoment B raw18831step1 raw18831step1Labels = mixedMoment B raw18831step2 raw18831step2Labels := by
      have ha : raw18831step2 = -raw18831step1 := by apply Matrix.ext; change ∀ i j, raw18831step2 i j = -(raw18831step1 i j); unfold raw18831step2 raw18831step1; decide +kernel
      have hl : raw18831step2Labels = raw18831step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw18832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18832step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18832 raw18832Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18832 raw18832Labels = mixedMoment B raw18832step0 raw18832step0Labels := by
      have hz : ∀ j, raw18832 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18832step0 = (fun i j => raw18832 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18832step0 raw18832; decide +kernel
      have hl : raw18832step0Labels = raw18832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18832 raw18832Labels permutation520 hz
    mixedMoment B raw18832step0 raw18832step0Labels = mixedMoment B raw18832step1 raw18832step1Labels := by
      have ha : raw18832step1 = (fun i j => raw18832step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18832step1 raw18832step0; decide +kernel
      have hl : raw18832step1Labels = raw18832step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18832step0 raw18832step0Labels permutation151 permutation2
    mixedMoment B raw18832step1 raw18832step1Labels = mixedMoment B raw18832step2 raw18832step2Labels := by
      have ha : raw18832step2 = -raw18832step1 := by apply Matrix.ext; change ∀ i j, raw18832step2 i j = -(raw18832step1 i j); unfold raw18832step2 raw18832step1; decide +kernel
      have hl : raw18832step2Labels = raw18832step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw18833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18833 raw18833Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw18833 raw18833Labels = mixedMoment B raw18833step0 raw18833step0Labels := by
      have ha : raw18833step0 = (fun i j => raw18833 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18833step0 raw18833; decide +kernel
      have hl : raw18833step0Labels = raw18833Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18833 raw18833Labels permutation269 permutation3
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw18834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18834 raw18834Labels = mixedMoment B node4011 node4011Labels := by
  calc
    mixedMoment B raw18834 raw18834Labels = mixedMoment B raw18834step0 raw18834step0Labels := by
      have ha : raw18834step0 = (fun i j => raw18834 (permutation615 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18834step0 raw18834; decide +kernel
      have hl : raw18834step0Labels = raw18834Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18834 raw18834Labels permutation615 permutation6
    _ = mixedMoment B node4011 node4011Labels := by rfl

def raw18835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18835 raw18835Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw18835 raw18835Labels = mixedMoment B raw18835step0 raw18835step0Labels := by
      have hz : ∀ j, raw18835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18835step0 = (fun i j => raw18835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18835step0 raw18835; decide +kernel
      have hl : raw18835step0Labels = raw18835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18835 raw18835Labels permutation434 hz
    mixedMoment B raw18835step0 raw18835step0Labels = mixedMoment B raw18835step1 raw18835step1Labels := by
      have ha : raw18835step1 = (fun i j => raw18835step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18835step1 raw18835step0; decide +kernel
      have hl : raw18835step1Labels = raw18835step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18835step0 raw18835step0Labels permutation138 permutation6
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw18836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18836step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18836 raw18836Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw18836 raw18836Labels = mixedMoment B raw18836step0 raw18836step0Labels := by
      have hz : ∀ j, raw18836 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18836step0 = (fun i j => raw18836 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18836step0 raw18836; decide +kernel
      have hl : raw18836step0Labels = raw18836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18836 raw18836Labels permutation520 hz
    mixedMoment B raw18836step0 raw18836step0Labels = mixedMoment B raw18836step1 raw18836step1Labels := by
      have ha : raw18836step1 = (fun i j => raw18836step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18836step1 raw18836step0; decide +kernel
      have hl : raw18836step1Labels = raw18836step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18836step0 raw18836step0Labels permutation138 permutation6
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw18837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18837 raw18837Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw18837 raw18837Labels = mixedMoment B raw18837step0 raw18837step0Labels := by
      have ha : raw18837step0 = (fun i j => raw18837 (permutation615 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18837step0 raw18837; decide +kernel
      have hl : raw18837step0Labels = raw18837Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18837 raw18837Labels permutation615 permutation6
    _ = mixedMoment B node3901 node3901Labels := by rfl

def raw18838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18838step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18838 raw18838Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw18838 raw18838Labels = mixedMoment B raw18838step0 raw18838step0Labels := by
      have hz : ∀ j, raw18838 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18838step0 = (fun i j => raw18838 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18838step0 raw18838; decide +kernel
      have hl : raw18838step0Labels = raw18838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18838 raw18838Labels permutation265 hz
    mixedMoment B raw18838step0 raw18838step0Labels = mixedMoment B raw18838step1 raw18838step1Labels := by
      have ha : raw18838step1 = (fun i j => raw18838step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18838step1 raw18838step0; decide +kernel
      have hl : raw18838step1Labels = raw18838step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18838step0 raw18838step0Labels permutation36 permutation3
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw18839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18839 raw18839Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw18839 raw18839Labels = mixedMoment B raw18839step0 raw18839step0Labels := by
      have hz : ∀ j, raw18839 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18839step0 = (fun i j => raw18839 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18839step0 raw18839; decide +kernel
      have hl : raw18839step0Labels = raw18839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18839 raw18839Labels permutation265 hz
    mixedMoment B raw18839step0 raw18839step0Labels = mixedMoment B raw18839step1 raw18839step1Labels := by
      have ha : raw18839step1 = (fun i j => raw18839step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18839step1 raw18839step0; decide +kernel
      have hl : raw18839step1Labels = raw18839step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18839step0 raw18839step0Labels permutation36 permutation3
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw18840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18840step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw18840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18840 raw18840Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw18840 raw18840Labels = mixedMoment B raw18840step0 raw18840step0Labels := by
      have hz : ∀ j, raw18840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18840step0 = (fun i j => raw18840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18840step0 raw18840; decide +kernel
      have hl : raw18840step0Labels = raw18840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18840 raw18840Labels permutation434 hz
    mixedMoment B raw18840step0 raw18840step0Labels = mixedMoment B raw18840step1 raw18840step1Labels := by
      have hz : ∀ j, raw18840step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw18840step1 = (fun i j => raw18840step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw18840step1 raw18840step0; decide +kernel
      have hl : raw18840step1Labels = raw18840step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18840step0 raw18840step0Labels permutation56 hz
    mixedMoment B raw18840step1 raw18840step1Labels = mixedMoment B raw18840step2 raw18840step2Labels := by
      have ha : raw18840step2 = (fun i j => raw18840step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18840step2 raw18840step1; decide +kernel
      have hl : raw18840step2Labels = raw18840step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18840step1 raw18840step1Labels permutation9 permutation3
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw18841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18841step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw18841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18841 raw18841Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw18841 raw18841Labels = mixedMoment B raw18841step0 raw18841step0Labels := by
      have hz : ∀ j, raw18841 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18841step0 = (fun i j => raw18841 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18841step0 raw18841; decide +kernel
      have hl : raw18841step0Labels = raw18841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18841 raw18841Labels permutation520 hz
    mixedMoment B raw18841step0 raw18841step0Labels = mixedMoment B raw18841step1 raw18841step1Labels := by
      have hz : ∀ j, raw18841step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw18841step1 = (fun i j => raw18841step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw18841step1 raw18841step0; decide +kernel
      have hl : raw18841step1Labels = raw18841step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18841step0 raw18841step0Labels permutation56 hz
    mixedMoment B raw18841step1 raw18841step1Labels = mixedMoment B raw18841step2 raw18841step2Labels := by
      have ha : raw18841step2 = (fun i j => raw18841step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18841step2 raw18841step1; decide +kernel
      have hl : raw18841step2Labels = raw18841step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18841step1 raw18841step1Labels permutation9 permutation3
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw18842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw18842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18842 raw18842Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw18842 raw18842Labels = mixedMoment B raw18842step0 raw18842step0Labels := by
      have hz : ∀ j, raw18842 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18842step0 = (fun i j => raw18842 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18842step0 raw18842; decide +kernel
      have hl : raw18842step0Labels = raw18842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18842 raw18842Labels permutation265 hz
    mixedMoment B raw18842step0 raw18842step0Labels = mixedMoment B raw18842step1 raw18842step1Labels := by
      have ha : raw18842step1 = (fun i j => raw18842step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18842step1 raw18842step0; decide +kernel
      have hl : raw18842step1Labels = raw18842step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18842step0 raw18842step0Labels permutation144 permutation6
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw18843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18843 raw18843Labels = mixedMoment B node2503 node2503Labels := by
  calc
    mixedMoment B raw18843 raw18843Labels = mixedMoment B raw18843step0 raw18843step0Labels := by
      have ha : raw18843step0 = (fun i j => raw18843 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18843step0 raw18843; decide +kernel
      have hl : raw18843step0Labels = raw18843Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18843 raw18843Labels permutation173 permutation3
    _ = mixedMoment B node2503 node2503Labels := by rfl

def raw18844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18844 raw18844Labels = mixedMoment B node3701 node3701Labels := by
  calc
    mixedMoment B raw18844 raw18844Labels = mixedMoment B raw18844step0 raw18844step0Labels := by
      have ha : raw18844step0 = (fun i j => raw18844 (permutation286 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18844step0 raw18844; decide +kernel
      have hl : raw18844step0Labels = raw18844Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18844 raw18844Labels permutation286 permutation3
    _ = mixedMoment B node3701 node3701Labels := by rfl

def raw18845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18845 raw18845Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw18845 raw18845Labels = mixedMoment B raw18845step0 raw18845step0Labels := by
      have hz : ∀ j, raw18845 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18845step0 = (fun i j => raw18845 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18845step0 raw18845; decide +kernel
      have hl : raw18845step0Labels = raw18845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18845 raw18845Labels permutation434 hz
    mixedMoment B raw18845step0 raw18845step0Labels = mixedMoment B raw18845step1 raw18845step1Labels := by
      have ha : raw18845step1 = (fun i j => raw18845step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18845step1 raw18845step0; decide +kernel
      have hl : raw18845step1Labels = raw18845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18845step0 raw18845step0Labels permutation37 permutation3
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw18846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18846step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18846 raw18846Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw18846 raw18846Labels = mixedMoment B raw18846step0 raw18846step0Labels := by
      have hz : ∀ j, raw18846 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18846step0 = (fun i j => raw18846 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18846step0 raw18846; decide +kernel
      have hl : raw18846step0Labels = raw18846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18846 raw18846Labels permutation520 hz
    mixedMoment B raw18846step0 raw18846step0Labels = mixedMoment B raw18846step1 raw18846step1Labels := by
      have ha : raw18846step1 = (fun i j => raw18846step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18846step1 raw18846step0; decide +kernel
      have hl : raw18846step1Labels = raw18846step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18846step0 raw18846step0Labels permutation37 permutation3
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw18847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18847 raw18847Labels = mixedMoment B node3900 node3900Labels := by
  calc
    mixedMoment B raw18847 raw18847Labels = mixedMoment B raw18847step0 raw18847step0Labels := by
      have ha : raw18847step0 = (fun i j => raw18847 (permutation615 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18847step0 raw18847; decide +kernel
      have hl : raw18847step0Labels = raw18847Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18847 raw18847Labels permutation615 permutation6
    _ = mixedMoment B node3900 node3900Labels := by rfl

def raw18848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18848 raw18848Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw18848 raw18848Labels = mixedMoment B raw18848step0 raw18848step0Labels := by
      have ha : raw18848step0 = (fun i j => raw18848 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18848step0 raw18848; decide +kernel
      have hl : raw18848step0Labels = raw18848Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18848 raw18848Labels permutation157 permutation3
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw18849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18849 raw18849Labels = mixedMoment B node3687 node3687Labels := by
  calc
    mixedMoment B raw18849 raw18849Labels = mixedMoment B raw18849step0 raw18849step0Labels := by
      have ha : raw18849step0 = (fun i j => raw18849 (permutation270 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18849step0 raw18849; decide +kernel
      have hl : raw18849step0Labels = raw18849Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18849 raw18849Labels permutation270 permutation3
    _ = mixedMoment B node3687 node3687Labels := by rfl

def raw18850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18850 raw18850Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw18850 raw18850Labels = mixedMoment B raw18850step0 raw18850step0Labels := by
      have ha : raw18850step0 = (fun i j => raw18850 (permutation504 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18850step0 raw18850; decide +kernel
      have hl : raw18850step0Labels = raw18850Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18850 raw18850Labels permutation504 permutation3
    mixedMoment B raw18850step0 raw18850step0Labels = mixedMoment B raw18850step1 raw18850step1Labels := by
      have ha : raw18850step1 = -raw18850step0 := by apply Matrix.ext; change ∀ i j, raw18850step1 i j = -(raw18850step0 i j); unfold raw18850step1 raw18850step0; decide +kernel
      have hl : raw18850step1Labels = raw18850step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw18851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18851 raw18851Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw18851 raw18851Labels = mixedMoment B raw18851step0 raw18851step0Labels := by
      have hz : ∀ j, raw18851 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18851step0 = (fun i j => raw18851 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18851step0 raw18851; decide +kernel
      have hl : raw18851step0Labels = raw18851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18851 raw18851Labels permutation520 hz
    mixedMoment B raw18851step0 raw18851step0Labels = mixedMoment B raw18851step1 raw18851step1Labels := by
      have ha : raw18851step1 = (fun i j => raw18851step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18851step1 raw18851step0; decide +kernel
      have hl : raw18851step1Labels = raw18851step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18851step0 raw18851step0Labels permutation127 permutation3
    mixedMoment B raw18851step1 raw18851step1Labels = mixedMoment B raw18851step2 raw18851step2Labels := by
      have ha : raw18851step2 = -raw18851step1 := by apply Matrix.ext; change ∀ i j, raw18851step2 i j = -(raw18851step1 i j); unfold raw18851step2 raw18851step1; decide +kernel
      have hl : raw18851step2Labels = raw18851step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw18852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18852 raw18852Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw18852 raw18852Labels = mixedMoment B raw18852step0 raw18852step0Labels := by
      have ha : raw18852step0 = (fun i j => raw18852 (permutation498 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18852step0 raw18852; decide +kernel
      have hl : raw18852step0Labels = raw18852Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18852 raw18852Labels permutation498 permutation3
    mixedMoment B raw18852step0 raw18852step0Labels = mixedMoment B raw18852step1 raw18852step1Labels := by
      have ha : raw18852step1 = -raw18852step0 := by apply Matrix.ext; change ∀ i j, raw18852step1 i j = -(raw18852step0 i j); unfold raw18852step1 raw18852step0; decide +kernel
      have hl : raw18852step1Labels = raw18852step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw18853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18853 raw18853Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw18853 raw18853Labels = mixedMoment B raw18853step0 raw18853step0Labels := by
      have ha : raw18853step0 = (fun i j => raw18853 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18853step0 raw18853; decide +kernel
      have hl : raw18853step0Labels = raw18853Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18853 raw18853Labels permutation156 permutation3
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw18854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18854 raw18854Labels = mixedMoment B node3687 node3687Labels := by
  calc
    mixedMoment B raw18854 raw18854Labels = mixedMoment B raw18854step0 raw18854step0Labels := by
      have ha : raw18854step0 = (fun i j => raw18854 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18854step0 raw18854; decide +kernel
      have hl : raw18854step0Labels = raw18854Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18854 raw18854Labels permutation269 permutation3
    _ = mixedMoment B node3687 node3687Labels := by rfl

def raw18855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18855 raw18855Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw18855 raw18855Labels = mixedMoment B raw18855step0 raw18855step0Labels := by
      have ha : raw18855step0 = (fun i j => raw18855 (permutation568 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18855step0 raw18855; decide +kernel
      have hl : raw18855step0Labels = raw18855Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18855 raw18855Labels permutation568 permutation3
    mixedMoment B raw18855step0 raw18855step0Labels = mixedMoment B raw18855step1 raw18855step1Labels := by
      have ha : raw18855step1 = -raw18855step0 := by apply Matrix.ext; change ∀ i j, raw18855step1 i j = -(raw18855step0 i j); unfold raw18855step1 raw18855step0; decide +kernel
      have hl : raw18855step1Labels = raw18855step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw18856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18856step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18856 raw18856Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw18856 raw18856Labels = mixedMoment B raw18856step0 raw18856step0Labels := by
      have hz : ∀ j, raw18856 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18856step0 = (fun i j => raw18856 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18856step0 raw18856; decide +kernel
      have hl : raw18856step0Labels = raw18856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18856 raw18856Labels permutation434 hz
    mixedMoment B raw18856step0 raw18856step0Labels = mixedMoment B raw18856step1 raw18856step1Labels := by
      have ha : raw18856step1 = (fun i j => raw18856step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18856step1 raw18856step0; decide +kernel
      have hl : raw18856step1Labels = raw18856step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18856step0 raw18856step0Labels permutation127 permutation3
    mixedMoment B raw18856step1 raw18856step1Labels = mixedMoment B raw18856step2 raw18856step2Labels := by
      have ha : raw18856step2 = -raw18856step1 := by apply Matrix.ext; change ∀ i j, raw18856step2 i j = -(raw18856step1 i j); unfold raw18856step2 raw18856step1; decide +kernel
      have hl : raw18856step2Labels = raw18856step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw18857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18857 raw18857Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw18857 raw18857Labels = mixedMoment B raw18857step0 raw18857step0Labels := by
      have ha : raw18857step0 = (fun i j => raw18857 (permutation562 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18857step0 raw18857; decide +kernel
      have hl : raw18857step0Labels = raw18857Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18857 raw18857Labels permutation562 permutation3
    mixedMoment B raw18857step0 raw18857step0Labels = mixedMoment B raw18857step1 raw18857step1Labels := by
      have ha : raw18857step1 = -raw18857step0 := by apply Matrix.ext; change ∀ i j, raw18857step1 i j = -(raw18857step0 i j); unfold raw18857step1 raw18857step0; decide +kernel
      have hl : raw18857step1Labels = raw18857step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw18858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18858 raw18858Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw18858 raw18858Labels = mixedMoment B raw18858step0 raw18858step0Labels := by
      have ha : raw18858step0 = (fun i j => raw18858 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18858step0 raw18858; decide +kernel
      have hl : raw18858step0Labels = raw18858Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18858 raw18858Labels permutation152 permutation3
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw18859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18859 raw18859Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw18859 raw18859Labels = mixedMoment B raw18859step0 raw18859step0Labels := by
      have ha : raw18859step0 = (fun i j => raw18859 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18859step0 raw18859; decide +kernel
      have hl : raw18859step0Labels = raw18859Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18859 raw18859Labels permutation265 permutation3
    _ = mixedMoment B node3692 node3692Labels := by rfl

def raw18860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18860 raw18860Labels = mixedMoment B node3967 node3967Labels := by
  calc
    mixedMoment B raw18860 raw18860Labels = mixedMoment B raw18860step0 raw18860step0Labels := by
      have ha : raw18860step0 = (fun i j => raw18860 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18860step0 raw18860; decide +kernel
      have hl : raw18860step0Labels = raw18860Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18860 raw18860Labels permutation152 permutation3
    _ = mixedMoment B node3967 node3967Labels := by rfl

def raw18861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18861step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18861 raw18861Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw18861 raw18861Labels = mixedMoment B raw18861step0 raw18861step0Labels := by
      have hz : ∀ j, raw18861 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18861step0 = (fun i j => raw18861 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18861step0 raw18861; decide +kernel
      have hl : raw18861step0Labels = raw18861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18861 raw18861Labels permutation434 hz
    mixedMoment B raw18861step0 raw18861step0Labels = mixedMoment B raw18861step1 raw18861step1Labels := by
      have ha : raw18861step1 = (fun i j => raw18861step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18861step1 raw18861step0; decide +kernel
      have hl : raw18861step1Labels = raw18861step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18861step0 raw18861step0Labels permutation32 permutation3
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw18862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18862step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18862 raw18862Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw18862 raw18862Labels = mixedMoment B raw18862step0 raw18862step0Labels := by
      have hz : ∀ j, raw18862 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18862step0 = (fun i j => raw18862 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18862step0 raw18862; decide +kernel
      have hl : raw18862step0Labels = raw18862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18862 raw18862Labels permutation520 hz
    mixedMoment B raw18862step0 raw18862step0Labels = mixedMoment B raw18862step1 raw18862step1Labels := by
      have ha : raw18862step1 = (fun i j => raw18862step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18862step1 raw18862step0; decide +kernel
      have hl : raw18862step1Labels = raw18862step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18862step0 raw18862step0Labels permutation32 permutation3
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw18863 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18863 raw18863Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw18863 raw18863Labels = mixedMoment B raw18863step0 raw18863step0Labels := by
      have ha : raw18863step0 = (fun i j => raw18863 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18863step0 raw18863; decide +kernel
      have hl : raw18863step0Labels = raw18863Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18863 raw18863Labels permutation184 permutation2
    mixedMoment B raw18863step0 raw18863step0Labels = mixedMoment B raw18863step1 raw18863step1Labels := by
      have ha : raw18863step1 = -raw18863step0 := by apply Matrix.ext; change ∀ i j, raw18863step1 i j = -(raw18863step0 i j); unfold raw18863step1 raw18863step0; decide +kernel
      have hl : raw18863step1Labels = raw18863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw18864 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18864step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18864 raw18864Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18864 raw18864Labels = mixedMoment B raw18864step0 raw18864step0Labels := by
      have hz : ∀ j, raw18864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18864step0 = (fun i j => raw18864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18864step0 raw18864; decide +kernel
      have hl : raw18864step0Labels = raw18864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18864 raw18864Labels permutation346 hz
    mixedMoment B raw18864step0 raw18864step0Labels = mixedMoment B raw18864step1 raw18864step1Labels := by
      have ha : raw18864step1 = (fun i j => raw18864step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18864step1 raw18864step0; decide +kernel
      have hl : raw18864step1Labels = raw18864step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18864step0 raw18864step0Labels permutation32 permutation7
    mixedMoment B raw18864step1 raw18864step1Labels = mixedMoment B raw18864step2 raw18864step2Labels := by
      have ha : raw18864step2 = raw18864step1 := by apply Matrix.ext; unfold raw18864step2 raw18864step1; decide +kernel
      have hl : raw18864step1Labels = labelEmbedding10 ∘ raw18864step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18864step1 raw18864step1Labels raw18864step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18865 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18865 raw18865Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18865 raw18865Labels = mixedMoment B raw18865step0 raw18865step0Labels := by
      have ha : raw18865step0 = (fun i j => raw18865 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18865step0 raw18865; decide +kernel
      have hl : raw18865step0Labels = raw18865Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18865 raw18865Labels permutation178 permutation2
    mixedMoment B raw18865step0 raw18865step0Labels = mixedMoment B raw18865step1 raw18865step1Labels := by
      have ha : raw18865step1 = -raw18865step0 := by apply Matrix.ext; change ∀ i j, raw18865step1 i j = -(raw18865step0 i j); unfold raw18865step1 raw18865step0; decide +kernel
      have hl : raw18865step1Labels = raw18865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18866 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18866 raw18866Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18866 raw18866Labels = mixedMoment B raw18866step0 raw18866step0Labels := by
      have ha : raw18866step0 = (fun i j => raw18866 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18866step0 raw18866; decide +kernel
      have hl : raw18866step0Labels = raw18866Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18866 raw18866Labels permutation176 permutation2
    mixedMoment B raw18866step0 raw18866step0Labels = mixedMoment B raw18866step1 raw18866step1Labels := by
      have ha : raw18866step1 = -raw18866step0 := by apply Matrix.ext; change ∀ i j, raw18866step1 i j = -(raw18866step0 i j); unfold raw18866step1 raw18866step0; decide +kernel
      have hl : raw18866step1Labels = raw18866step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18867 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18867step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18867 raw18867Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw18867 raw18867Labels = mixedMoment B raw18867step0 raw18867step0Labels := by
      have ha : raw18867step0 = (fun i j => raw18867 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18867step0 raw18867; decide +kernel
      have hl : raw18867step0Labels = raw18867Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18867 raw18867Labels permutation616 permutation3
    mixedMoment B raw18867step0 raw18867step0Labels = mixedMoment B raw18867step1 raw18867step1Labels := by
      have ha : raw18867step1 = raw18867step0 := by apply Matrix.ext; unfold raw18867step1 raw18867step0; decide +kernel
      have hl : raw18867step0Labels = labelEmbedding6 ∘ raw18867step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18867step0 raw18867step0Labels raw18867step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw18868 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18868step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18868 raw18868Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18868 raw18868Labels = mixedMoment B raw18868step0 raw18868step0Labels := by
      have ha : raw18868step0 = (fun i j => raw18868 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18868step0 raw18868; decide +kernel
      have hl : raw18868step0Labels = raw18868Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18868 raw18868Labels permutation156 permutation6
    mixedMoment B raw18868step0 raw18868step0Labels = mixedMoment B raw18868step1 raw18868step1Labels := by
      have ha : raw18868step1 = raw18868step0 := by apply Matrix.ext; unfold raw18868step1 raw18868step0; decide +kernel
      have hl : raw18868step0Labels = labelEmbedding9 ∘ raw18868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18868step0 raw18868step0Labels raw18868step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw18869 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18869step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18869step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18869 raw18869Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18869 raw18869Labels = mixedMoment B raw18869step0 raw18869step0Labels := by
      have hz : ∀ j, raw18869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18869step0 = (fun i j => raw18869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18869step0 raw18869; decide +kernel
      have hl : raw18869step0Labels = raw18869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18869 raw18869Labels permutation346 hz
    mixedMoment B raw18869step0 raw18869step0Labels = mixedMoment B raw18869step1 raw18869step1Labels := by
      have ha : raw18869step1 = (fun i j => raw18869step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18869step1 raw18869step0; decide +kernel
      have hl : raw18869step1Labels = raw18869step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18869step0 raw18869step0Labels permutation32 permutation7
    mixedMoment B raw18869step1 raw18869step1Labels = mixedMoment B raw18869step2 raw18869step2Labels := by
      have ha : raw18869step2 = raw18869step1 := by apply Matrix.ext; unfold raw18869step2 raw18869step1; decide +kernel
      have hl : raw18869step1Labels = labelEmbedding10 ∘ raw18869step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18869step1 raw18869step1Labels raw18869step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw18870 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18870 raw18870Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw18870 raw18870Labels = mixedMoment B raw18870step0 raw18870step0Labels := by
      have ha : raw18870step0 = (fun i j => raw18870 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18870step0 raw18870; decide +kernel
      have hl : raw18870step0Labels = raw18870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18870 raw18870Labels permutation664 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw18871 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18871 raw18871Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw18871 raw18871Labels = mixedMoment B raw18871step0 raw18871step0Labels := by
      have ha : raw18871step0 = (fun i j => raw18871 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18871step0 raw18871; decide +kernel
      have hl : raw18871step0Labels = raw18871Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18871 raw18871Labels permutation688 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw18872 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18872step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18872 raw18872Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw18872 raw18872Labels = mixedMoment B raw18872step0 raw18872step0Labels := by
      have ha : raw18872step0 = (fun i j => raw18872 (permutation659 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18872step0 raw18872; decide +kernel
      have hl : raw18872step0Labels = raw18872Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18872 raw18872Labels permutation659 permutation3
    mixedMoment B raw18872step0 raw18872step0Labels = mixedMoment B raw18872step1 raw18872step1Labels := by
      have ha : raw18872step1 = raw18872step0 := by apply Matrix.ext; unfold raw18872step1 raw18872step0; decide +kernel
      have hl : raw18872step0Labels = labelEmbedding6 ∘ raw18872step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18872step0 raw18872step0Labels raw18872step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw18873 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18873step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18873step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18873step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18873 raw18873Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw18873 raw18873Labels = mixedMoment B raw18873step0 raw18873step0Labels := by
      have ha : raw18873step0 = (fun i j => raw18873 (permutation173 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18873step0 raw18873; decide +kernel
      have hl : raw18873step0Labels = raw18873Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18873 raw18873Labels permutation173 permutation4
    mixedMoment B raw18873step0 raw18873step0Labels = mixedMoment B raw18873step1 raw18873step1Labels := by
      have ha : raw18873step1 = -raw18873step0 := by apply Matrix.ext; change ∀ i j, raw18873step1 i j = -(raw18873step0 i j); unfold raw18873step1 raw18873step0; decide +kernel
      have hl : raw18873step1Labels = raw18873step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18873step1 raw18873step1Labels = mixedMoment B raw18873step2 raw18873step2Labels := by
      have ha : raw18873step2 = raw18873step1 := by apply Matrix.ext; unfold raw18873step2 raw18873step1; decide +kernel
      have hl : raw18873step1Labels = labelEmbedding7 ∘ raw18873step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18873step1 raw18873step1Labels raw18873step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw18874 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18874step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18874 raw18874Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw18874 raw18874Labels = mixedMoment B raw18874step0 raw18874step0Labels := by
      have ha : raw18874step0 = (fun i j => raw18874 (permutation390 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18874step0 raw18874; decide +kernel
      have hl : raw18874step0Labels = raw18874Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18874 raw18874Labels permutation390 permutation5
    mixedMoment B raw18874step0 raw18874step0Labels = mixedMoment B raw18874step1 raw18874step1Labels := by
      have ha : raw18874step1 = raw18874step0 := by apply Matrix.ext; unfold raw18874step1 raw18874step0; decide +kernel
      have hl : raw18874step0Labels = labelEmbedding8 ∘ raw18874step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18874step0 raw18874step0Labels raw18874step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw18875 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18875step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18875step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18875 raw18875Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18875 raw18875Labels = mixedMoment B raw18875step0 raw18875step0Labels := by
      have ha : raw18875step0 = (fun i j => raw18875 (permutation407 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18875step0 raw18875; decide +kernel
      have hl : raw18875step0Labels = raw18875Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18875 raw18875Labels permutation407 permutation5
    mixedMoment B raw18875step0 raw18875step0Labels = mixedMoment B raw18875step1 raw18875step1Labels := by
      have ha : raw18875step1 = raw18875step0 := by apply Matrix.ext; unfold raw18875step1 raw18875step0; decide +kernel
      have hl : raw18875step0Labels = labelEmbedding8 ∘ raw18875step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18875step0 raw18875step0Labels raw18875step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18876 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18876step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18876 raw18876Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18876 raw18876Labels = mixedMoment B raw18876step0 raw18876step0Labels := by
      have ha : raw18876step0 = (fun i j => raw18876 (permutation389 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18876step0 raw18876; decide +kernel
      have hl : raw18876step0Labels = raw18876Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18876 raw18876Labels permutation389 permutation5
    mixedMoment B raw18876step0 raw18876step0Labels = mixedMoment B raw18876step1 raw18876step1Labels := by
      have ha : raw18876step1 = raw18876step0 := by apply Matrix.ext; unfold raw18876step1 raw18876step0; decide +kernel
      have hl : raw18876step0Labels = labelEmbedding8 ∘ raw18876step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18876step0 raw18876step0Labels raw18876step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18877 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18877step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18877step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18877 raw18877Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw18877 raw18877Labels = mixedMoment B raw18877step0 raw18877step0Labels := by
      have ha : raw18877step0 = (fun i j => raw18877 (permutation615 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18877step0 raw18877; decide +kernel
      have hl : raw18877step0Labels = raw18877Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18877 raw18877Labels permutation615 permutation3
    mixedMoment B raw18877step0 raw18877step0Labels = mixedMoment B raw18877step1 raw18877step1Labels := by
      have ha : raw18877step1 = raw18877step0 := by apply Matrix.ext; unfold raw18877step1 raw18877step0; decide +kernel
      have hl : raw18877step0Labels = labelEmbedding6 ∘ raw18877step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18877step0 raw18877step0Labels raw18877step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw18878 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18878step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18878step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18878step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18878step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18878 raw18878Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18878 raw18878Labels = mixedMoment B raw18878step0 raw18878step0Labels := by
      have ha : raw18878step0 = (fun i j => raw18878 (permutation171 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18878step0 raw18878; decide +kernel
      have hl : raw18878step0Labels = raw18878Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18878 raw18878Labels permutation171 permutation4
    mixedMoment B raw18878step0 raw18878step0Labels = mixedMoment B raw18878step1 raw18878step1Labels := by
      have ha : raw18878step1 = -raw18878step0 := by apply Matrix.ext; change ∀ i j, raw18878step1 i j = -(raw18878step0 i j); unfold raw18878step1 raw18878step0; decide +kernel
      have hl : raw18878step1Labels = raw18878step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18878step1 raw18878step1Labels = mixedMoment B raw18878step2 raw18878step2Labels := by
      have ha : raw18878step2 = raw18878step1 := by apply Matrix.ext; unfold raw18878step2 raw18878step1; decide +kernel
      have hl : raw18878step1Labels = labelEmbedding7 ∘ raw18878step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18878step1 raw18878step1Labels raw18878step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw18879 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18879step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18879step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18879step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18879 raw18879Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw18879 raw18879Labels = mixedMoment B raw18879step0 raw18879step0Labels := by
      have ha : raw18879step0 = (fun i j => raw18879 (permutation284 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18879step0 raw18879; decide +kernel
      have hl : raw18879step0Labels = raw18879Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18879 raw18879Labels permutation284 permutation4
    mixedMoment B raw18879step0 raw18879step0Labels = mixedMoment B raw18879step1 raw18879step1Labels := by
      have ha : raw18879step1 = -raw18879step0 := by apply Matrix.ext; change ∀ i j, raw18879step1 i j = -(raw18879step0 i j); unfold raw18879step1 raw18879step0; decide +kernel
      have hl : raw18879step1Labels = raw18879step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18879step1 raw18879step1Labels = mixedMoment B raw18879step2 raw18879step2Labels := by
      have ha : raw18879step2 = raw18879step1 := by apply Matrix.ext; unfold raw18879step2 raw18879step1; decide +kernel
      have hl : raw18879step1Labels = labelEmbedding7 ∘ raw18879step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18879step1 raw18879step1Labels raw18879step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw18880 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18880step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18880 raw18880Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18880 raw18880Labels = mixedMoment B raw18880step0 raw18880step0Labels := by
      have hz : ∀ j, raw18880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18880step0 = (fun i j => raw18880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18880step0 raw18880; decide +kernel
      have hl : raw18880step0Labels = raw18880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18880 raw18880Labels permutation346 hz
    mixedMoment B raw18880step0 raw18880step0Labels = mixedMoment B raw18880step1 raw18880step1Labels := by
      have ha : raw18880step1 = (fun i j => raw18880step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18880step1 raw18880step0; decide +kernel
      have hl : raw18880step1Labels = raw18880step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18880step0 raw18880step0Labels permutation97 permutation4
    mixedMoment B raw18880step1 raw18880step1Labels = mixedMoment B raw18880step2 raw18880step2Labels := by
      have ha : raw18880step2 = raw18880step1 := by apply Matrix.ext; unfold raw18880step2 raw18880step1; decide +kernel
      have hl : raw18880step1Labels = labelEmbedding7 ∘ raw18880step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18880step1 raw18880step1Labels raw18880step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw18881 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18881 raw18881Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw18881 raw18881Labels = mixedMoment B raw18881step0 raw18881step0Labels := by
      have ha : raw18881step0 = (fun i j => raw18881 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18881step0 raw18881; decide +kernel
      have hl : raw18881step0Labels = raw18881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18881 raw18881Labels permutation676 permutation2
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw18882 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18882step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18882 raw18882Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw18882 raw18882Labels = mixedMoment B raw18882step0 raw18882step0Labels := by
      have ha : raw18882step0 = (fun i j => raw18882 (permutation617 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18882step0 raw18882; decide +kernel
      have hl : raw18882step0Labels = raw18882Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18882 raw18882Labels permutation617 permutation3
    mixedMoment B raw18882step0 raw18882step0Labels = mixedMoment B raw18882step1 raw18882step1Labels := by
      have ha : raw18882step1 = raw18882step0 := by apply Matrix.ext; unfold raw18882step1 raw18882step0; decide +kernel
      have hl : raw18882step0Labels = labelEmbedding6 ∘ raw18882step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18882step0 raw18882step0Labels raw18882step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw18883 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18883step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18883step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18883step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18883step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18883step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18883 raw18883Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18883 raw18883Labels = mixedMoment B raw18883step0 raw18883step0Labels := by
      have ha : raw18883step0 = (fun i j => raw18883 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18883step0 raw18883; decide +kernel
      have hl : raw18883step0Labels = raw18883Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18883 raw18883Labels permutation170 permutation4
    mixedMoment B raw18883step0 raw18883step0Labels = mixedMoment B raw18883step1 raw18883step1Labels := by
      have ha : raw18883step1 = -raw18883step0 := by apply Matrix.ext; change ∀ i j, raw18883step1 i j = -(raw18883step0 i j); unfold raw18883step1 raw18883step0; decide +kernel
      have hl : raw18883step1Labels = raw18883step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18883step1 raw18883step1Labels = mixedMoment B raw18883step2 raw18883step2Labels := by
      have ha : raw18883step2 = raw18883step1 := by apply Matrix.ext; unfold raw18883step2 raw18883step1; decide +kernel
      have hl : raw18883step1Labels = labelEmbedding7 ∘ raw18883step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18883step1 raw18883step1Labels raw18883step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw18884 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18884step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18884step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18884step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18884 raw18884Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw18884 raw18884Labels = mixedMoment B raw18884step0 raw18884step0Labels := by
      have ha : raw18884step0 = (fun i j => raw18884 (permutation283 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18884step0 raw18884; decide +kernel
      have hl : raw18884step0Labels = raw18884Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18884 raw18884Labels permutation283 permutation4
    mixedMoment B raw18884step0 raw18884step0Labels = mixedMoment B raw18884step1 raw18884step1Labels := by
      have ha : raw18884step1 = -raw18884step0 := by apply Matrix.ext; change ∀ i j, raw18884step1 i j = -(raw18884step0 i j); unfold raw18884step1 raw18884step0; decide +kernel
      have hl : raw18884step1Labels = raw18884step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18884step1 raw18884step1Labels = mixedMoment B raw18884step2 raw18884step2Labels := by
      have ha : raw18884step2 = raw18884step1 := by apply Matrix.ext; unfold raw18884step2 raw18884step1; decide +kernel
      have hl : raw18884step1Labels = labelEmbedding7 ∘ raw18884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18884step1 raw18884step1Labels raw18884step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw18885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18885step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18885step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18885 raw18885Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18885 raw18885Labels = mixedMoment B raw18885step0 raw18885step0Labels := by
      have hz : ∀ j, raw18885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18885step0 = (fun i j => raw18885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18885step0 raw18885; decide +kernel
      have hl : raw18885step0Labels = raw18885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18885 raw18885Labels permutation346 hz
    mixedMoment B raw18885step0 raw18885step0Labels = mixedMoment B raw18885step1 raw18885step1Labels := by
      have ha : raw18885step1 = (fun i j => raw18885step0 (permutation121 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18885step1 raw18885step0; decide +kernel
      have hl : raw18885step1Labels = raw18885step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18885step0 raw18885step0Labels permutation121 permutation4
    mixedMoment B raw18885step1 raw18885step1Labels = mixedMoment B raw18885step2 raw18885step2Labels := by
      have ha : raw18885step2 = raw18885step1 := by apply Matrix.ext; unfold raw18885step2 raw18885step1; decide +kernel
      have hl : raw18885step1Labels = labelEmbedding7 ∘ raw18885step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18885step1 raw18885step1Labels raw18885step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw18886 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18886 raw18886Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw18886 raw18886Labels = mixedMoment B raw18886step0 raw18886step0Labels := by
      have ha : raw18886step0 = (fun i j => raw18886 (permutation654 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18886step0 raw18886; decide +kernel
      have hl : raw18886step0Labels = raw18886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18886 raw18886Labels permutation654 permutation2
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw18887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw18887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18887step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18887 raw18887Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw18887 raw18887Labels = mixedMoment B raw18887step0 raw18887step0Labels := by
      have ha : raw18887step0 = (fun i j => raw18887 (permutation612 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18887step0 raw18887; decide +kernel
      have hl : raw18887step0Labels = raw18887Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18887 raw18887Labels permutation612 permutation3
    mixedMoment B raw18887step0 raw18887step0Labels = mixedMoment B raw18887step1 raw18887step1Labels := by
      have ha : raw18887step1 = raw18887step0 := by apply Matrix.ext; unfold raw18887step1 raw18887step0; decide +kernel
      have hl : raw18887step0Labels = labelEmbedding6 ∘ raw18887step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18887step0 raw18887step0Labels raw18887step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw18888 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18888step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18888step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18888step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18888 raw18888Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw18888 raw18888Labels = mixedMoment B raw18888step0 raw18888step0Labels := by
      have ha : raw18888step0 = (fun i j => raw18888 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18888step0 raw18888; decide +kernel
      have hl : raw18888step0Labels = raw18888Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18888 raw18888Labels permutation170 permutation4
    mixedMoment B raw18888step0 raw18888step0Labels = mixedMoment B raw18888step1 raw18888step1Labels := by
      have ha : raw18888step1 = -raw18888step0 := by apply Matrix.ext; change ∀ i j, raw18888step1 i j = -(raw18888step0 i j); unfold raw18888step1 raw18888step0; decide +kernel
      have hl : raw18888step1Labels = raw18888step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18888step1 raw18888step1Labels = mixedMoment B raw18888step2 raw18888step2Labels := by
      have ha : raw18888step2 = raw18888step1 := by apply Matrix.ext; unfold raw18888step2 raw18888step1; decide +kernel
      have hl : raw18888step1Labels = labelEmbedding7 ∘ raw18888step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18888step1 raw18888step1Labels raw18888step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw18889 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18889step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18889step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18889step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18889 raw18889Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw18889 raw18889Labels = mixedMoment B raw18889step0 raw18889step0Labels := by
      have ha : raw18889step0 = (fun i j => raw18889 (permutation283 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18889step0 raw18889; decide +kernel
      have hl : raw18889step0Labels = raw18889Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18889 raw18889Labels permutation283 permutation4
    mixedMoment B raw18889step0 raw18889step0Labels = mixedMoment B raw18889step1 raw18889step1Labels := by
      have ha : raw18889step1 = -raw18889step0 := by apply Matrix.ext; change ∀ i j, raw18889step1 i j = -(raw18889step0 i j); unfold raw18889step1 raw18889step0; decide +kernel
      have hl : raw18889step1Labels = raw18889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18889step1 raw18889step1Labels = mixedMoment B raw18889step2 raw18889step2Labels := by
      have ha : raw18889step2 = raw18889step1 := by apply Matrix.ext; unfold raw18889step2 raw18889step1; decide +kernel
      have hl : raw18889step1Labels = labelEmbedding7 ∘ raw18889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18889step1 raw18889step1Labels raw18889step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw18890 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18890step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18890 raw18890Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw18890 raw18890Labels = mixedMoment B raw18890step0 raw18890step0Labels := by
      have hz : ∀ j, raw18890 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18890step0 = (fun i j => raw18890 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18890step0 raw18890; decide +kernel
      have hl : raw18890step0Labels = raw18890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18890 raw18890Labels permutation346 hz
    mixedMoment B raw18890step0 raw18890step0Labels = mixedMoment B raw18890step1 raw18890step1Labels := by
      have ha : raw18890step1 = (fun i j => raw18890step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18890step1 raw18890step0; decide +kernel
      have hl : raw18890step1Labels = raw18890step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18890step0 raw18890step0Labels permutation36 permutation6
    mixedMoment B raw18890step1 raw18890step1Labels = mixedMoment B raw18890step2 raw18890step2Labels := by
      have ha : raw18890step2 = raw18890step1 := by apply Matrix.ext; unfold raw18890step2 raw18890step1; decide +kernel
      have hl : raw18890step1Labels = labelEmbedding9 ∘ raw18890step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18890step1 raw18890step1Labels raw18890step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw18891 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18891step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18891 raw18891Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18891 raw18891Labels = mixedMoment B raw18891step0 raw18891step0Labels := by
      have ha : raw18891step0 = (fun i j => raw18891 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18891step0 raw18891; decide +kernel
      have hl : raw18891step0Labels = raw18891Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18891 raw18891Labels permutation153 permutation6
    mixedMoment B raw18891step0 raw18891step0Labels = mixedMoment B raw18891step1 raw18891step1Labels := by
      have ha : raw18891step1 = raw18891step0 := by apply Matrix.ext; unfold raw18891step1 raw18891step0; decide +kernel
      have hl : raw18891step0Labels = labelEmbedding9 ∘ raw18891step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18891step0 raw18891step0Labels raw18891step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw18892 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18892step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18892 raw18892Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18892 raw18892Labels = mixedMoment B raw18892step0 raw18892step0Labels := by
      have ha : raw18892step0 = (fun i j => raw18892 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18892step0 raw18892; decide +kernel
      have hl : raw18892step0Labels = raw18892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18892 raw18892Labels permutation155 permutation6
    mixedMoment B raw18892step0 raw18892step0Labels = mixedMoment B raw18892step1 raw18892step1Labels := by
      have ha : raw18892step1 = raw18892step0 := by apply Matrix.ext; unfold raw18892step1 raw18892step0; decide +kernel
      have hl : raw18892step0Labels = labelEmbedding9 ∘ raw18892step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18892step0 raw18892step0Labels raw18892step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw18893 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18893Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18893 raw18893Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw18893 raw18893Labels = mixedMoment B raw18893step0 raw18893step0Labels := by
      have ha : raw18893step0 = (fun i j => raw18893 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18893step0 raw18893; decide +kernel
      have hl : raw18893step0Labels = raw18893Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18893 raw18893Labels permutation616 permutation3
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw18894 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18894Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18894step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18894 raw18894Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw18894 raw18894Labels = mixedMoment B raw18894step0 raw18894step0Labels := by
      have hz : ∀ j, raw18894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18894step0 = (fun i j => raw18894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18894step0 raw18894; decide +kernel
      have hl : raw18894step0Labels = raw18894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18894 raw18894Labels permutation346 hz
    mixedMoment B raw18894step0 raw18894step0Labels = mixedMoment B raw18894step1 raw18894step1Labels := by
      have ha : raw18894step1 = (fun i j => raw18894step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18894step1 raw18894step0; decide +kernel
      have hl : raw18894step1Labels = raw18894step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18894step0 raw18894step0Labels permutation137 permutation3
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw18895 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18895 raw18895Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw18895 raw18895Labels = mixedMoment B raw18895step0 raw18895step0Labels := by
      have ha : raw18895step0 = (fun i j => raw18895 (permutation654 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18895step0 raw18895; decide +kernel
      have hl : raw18895step0Labels = raw18895Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18895 raw18895Labels permutation654 permutation3
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw18896 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18896 raw18896Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw18896 raw18896Labels = mixedMoment B raw18896step0 raw18896step0Labels := by
      have ha : raw18896step0 = (fun i j => raw18896 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18896step0 raw18896; decide +kernel
      have hl : raw18896step0Labels = raw18896Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18896 raw18896Labels permutation676 permutation3
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw18897 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18897 raw18897Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw18897 raw18897Labels = mixedMoment B raw18897step0 raw18897step0Labels := by
      have ha : raw18897step0 = (fun i j => raw18897 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18897step0 raw18897; decide +kernel
      have hl : raw18897step0Labels = raw18897Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18897 raw18897Labels permutation616 permutation3
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw18898 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18898 raw18898Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw18898 raw18898Labels = mixedMoment B raw18898step0 raw18898step0Labels := by
      have ha : raw18898step0 = (fun i j => raw18898 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18898step0 raw18898; decide +kernel
      have hl : raw18898step0Labels = raw18898Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18898 raw18898Labels permutation156 permutation6
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw18899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18899step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18899 raw18899Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw18899 raw18899Labels = mixedMoment B raw18899step0 raw18899step0Labels := by
      have hz : ∀ j, raw18899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18899step0 = (fun i j => raw18899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18899step0 raw18899; decide +kernel
      have hl : raw18899step0Labels = raw18899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18899 raw18899Labels permutation346 hz
    mixedMoment B raw18899step0 raw18899step0Labels = mixedMoment B raw18899step1 raw18899step1Labels := by
      have ha : raw18899step1 = (fun i j => raw18899step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18899step1 raw18899step0; decide +kernel
      have hl : raw18899step1Labels = raw18899step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18899step0 raw18899step0Labels permutation36 permutation6
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw18900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18900Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18900 raw18900Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw18900 raw18900Labels = mixedMoment B raw18900step0 raw18900step0Labels := by
      have ha : raw18900step0 = (fun i j => raw18900 (permutation659 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18900step0 raw18900; decide +kernel
      have hl : raw18900step0Labels = raw18900Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18900 raw18900Labels permutation659 permutation3
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw18901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18901Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18901 raw18901Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw18901 raw18901Labels = mixedMoment B raw18901step0 raw18901step0Labels := by
      have ha : raw18901step0 = (fun i j => raw18901 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18901step0 raw18901; decide +kernel
      have hl : raw18901step0Labels = raw18901Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18901 raw18901Labels permutation683 permutation3
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw18902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18902Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18902 raw18902Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw18902 raw18902Labels = mixedMoment B raw18902step0 raw18902step0Labels := by
      have ha : raw18902step0 = (fun i j => raw18902 (permutation659 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18902step0 raw18902; decide +kernel
      have hl : raw18902step0Labels = raw18902Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18902 raw18902Labels permutation659 permutation3
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw18903 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18903Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18903 raw18903Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw18903 raw18903Labels = mixedMoment B raw18903step0 raw18903step0Labels := by
      have ha : raw18903step0 = (fun i j => raw18903 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18903step0 raw18903; decide +kernel
      have hl : raw18903step0Labels = raw18903Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18903 raw18903Labels permutation156 permutation6
    _ = mixedMoment B node3810 node3810Labels := by rfl

def raw18904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18904 raw18904Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw18904 raw18904Labels = mixedMoment B raw18904step0 raw18904step0Labels := by
      have ha : raw18904step0 = (fun i j => raw18904 (permutation354 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18904step0 raw18904; decide +kernel
      have hl : raw18904step0Labels = raw18904Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18904 raw18904Labels permutation354 permutation3
    mixedMoment B raw18904step0 raw18904step0Labels = mixedMoment B raw18904step1 raw18904step1Labels := by
      have ha : raw18904step1 = -raw18904step0 := by apply Matrix.ext; change ∀ i j, raw18904step1 i j = -(raw18904step0 i j); unfold raw18904step1 raw18904step0; decide +kernel
      have hl : raw18904step1Labels = raw18904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3869 node3869Labels := by rfl

def raw18905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18905 raw18905Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw18905 raw18905Labels = mixedMoment B raw18905step0 raw18905step0Labels := by
      have ha : raw18905step0 = (fun i j => raw18905 (permutation356 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18905step0 raw18905; decide +kernel
      have hl : raw18905step0Labels = raw18905Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18905 raw18905Labels permutation356 permutation3
    mixedMoment B raw18905step0 raw18905step0Labels = mixedMoment B raw18905step1 raw18905step1Labels := by
      have ha : raw18905step1 = -raw18905step0 := by apply Matrix.ext; change ∀ i j, raw18905step1 i j = -(raw18905step0 i j); unfold raw18905step1 raw18905step0; decide +kernel
      have hl : raw18905step1Labels = raw18905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw18906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18906 raw18906Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw18906 raw18906Labels = mixedMoment B raw18906step0 raw18906step0Labels := by
      have ha : raw18906step0 = (fun i j => raw18906 (permutation352 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18906step0 raw18906; decide +kernel
      have hl : raw18906step0Labels = raw18906Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18906 raw18906Labels permutation352 permutation3
    mixedMoment B raw18906step0 raw18906step0Labels = mixedMoment B raw18906step1 raw18906step1Labels := by
      have ha : raw18906step1 = -raw18906step0 := by apply Matrix.ext; change ∀ i j, raw18906step1 i j = -(raw18906step0 i j); unfold raw18906step1 raw18906step0; decide +kernel
      have hl : raw18906step1Labels = raw18906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw18907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18907 raw18907Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw18907 raw18907Labels = mixedMoment B raw18907step0 raw18907step0Labels := by
      have ha : raw18907step0 = (fun i j => raw18907 (permutation615 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18907step0 raw18907; decide +kernel
      have hl : raw18907step0Labels = raw18907Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18907 raw18907Labels permutation615 permutation3
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw18908 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18908 raw18908Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw18908 raw18908Labels = mixedMoment B raw18908step0 raw18908step0Labels := by
      have ha : raw18908step0 = (fun i j => raw18908 (permutation157 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18908step0 raw18908; decide +kernel
      have hl : raw18908step0Labels = raw18908Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18908 raw18908Labels permutation157 permutation6
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw18909 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18909 raw18909Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw18909 raw18909Labels = mixedMoment B raw18909step0 raw18909step0Labels := by
      have ha : raw18909step0 = (fun i j => raw18909 (permutation617 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18909step0 raw18909; decide +kernel
      have hl : raw18909step0Labels = raw18909Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18909 raw18909Labels permutation617 permutation3
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw18910 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18910 raw18910Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw18910 raw18910Labels = mixedMoment B raw18910step0 raw18910step0Labels := by
      have hz : ∀ j, raw18910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18910step0 = (fun i j => raw18910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18910step0 raw18910; decide +kernel
      have hl : raw18910step0Labels = raw18910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18910 raw18910Labels permutation346 hz
    mixedMoment B raw18910step0 raw18910step0Labels = mixedMoment B raw18910step1 raw18910step1Labels := by
      have ha : raw18910step1 = (fun i j => raw18910step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18910step1 raw18910step0; decide +kernel
      have hl : raw18910step1Labels = raw18910step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18910step0 raw18910step0Labels permutation37 permutation6
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw18911 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18911 raw18911Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw18911 raw18911Labels = mixedMoment B raw18911step0 raw18911step0Labels := by
      have ha : raw18911step0 = (fun i j => raw18911 (permutation157 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18911step0 raw18911; decide +kernel
      have hl : raw18911step0Labels = raw18911Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18911 raw18911Labels permutation157 permutation6
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw18912 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18912 raw18912Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw18912 raw18912Labels = mixedMoment B raw18912step0 raw18912step0Labels := by
      have ha : raw18912step0 = (fun i j => raw18912 (permutation617 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18912step0 raw18912; decide +kernel
      have hl : raw18912step0Labels = raw18912Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18912 raw18912Labels permutation617 permutation3
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw18913 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18913 raw18913Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw18913 raw18913Labels = mixedMoment B raw18913step0 raw18913step0Labels := by
      have ha : raw18913step0 = (fun i j => raw18913 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18913step0 raw18913; decide +kernel
      have hl : raw18913step0Labels = raw18913Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18913 raw18913Labels permutation156 permutation6
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw18914 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18914 raw18914Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw18914 raw18914Labels = mixedMoment B raw18914step0 raw18914step0Labels := by
      have ha : raw18914step0 = (fun i j => raw18914 (permutation612 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18914step0 raw18914; decide +kernel
      have hl : raw18914step0Labels = raw18914Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18914 raw18914Labels permutation612 permutation3
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw18915 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18915 raw18915Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw18915 raw18915Labels = mixedMoment B raw18915step0 raw18915step0Labels := by
      have hz : ∀ j, raw18915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18915step0 = (fun i j => raw18915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18915step0 raw18915; decide +kernel
      have hl : raw18915step0Labels = raw18915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18915 raw18915Labels permutation346 hz
    mixedMoment B raw18915step0 raw18915step0Labels = mixedMoment B raw18915step1 raw18915step1Labels := by
      have ha : raw18915step1 = (fun i j => raw18915step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18915step1 raw18915step0; decide +kernel
      have hl : raw18915step1Labels = raw18915step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18915step0 raw18915step0Labels permutation36 permutation6
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw18916 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18916 raw18916Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw18916 raw18916Labels = mixedMoment B raw18916step0 raw18916step0Labels := by
      have ha : raw18916step0 = (fun i j => raw18916 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18916step0 raw18916; decide +kernel
      have hl : raw18916step0Labels = raw18916Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18916 raw18916Labels permutation156 permutation6
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw18917 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw18917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18917 raw18917Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw18917 raw18917Labels = mixedMoment B raw18917step0 raw18917step0Labels := by
      have ha : raw18917step0 = (fun i j => raw18917 (permutation612 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18917step0 raw18917; decide +kernel
      have hl : raw18917step0Labels = raw18917Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18917 raw18917Labels permutation612 permutation3
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw18918 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18918 raw18918Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw18918 raw18918Labels = mixedMoment B raw18918step0 raw18918step0Labels := by
      have ha : raw18918step0 = (fun i j => raw18918 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18918step0 raw18918; decide +kernel
      have hl : raw18918step0Labels = raw18918Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18918 raw18918Labels permutation156 permutation6
    _ = mixedMoment B node3806 node3806Labels := by rfl

def raw18919 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18919 raw18919Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw18919 raw18919Labels = mixedMoment B raw18919step0 raw18919step0Labels := by
      have ha : raw18919step0 = (fun i j => raw18919 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18919step0 raw18919; decide +kernel
      have hl : raw18919step0Labels = raw18919Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18919 raw18919Labels permutation156 permutation6
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw18920 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18920step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18920 raw18920Labels = mixedMoment B node3985 node3985Labels := by
  calc
    mixedMoment B raw18920 raw18920Labels = mixedMoment B raw18920step0 raw18920step0Labels := by
      have hz : ∀ j, raw18920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18920step0 = (fun i j => raw18920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18920step0 raw18920; decide +kernel
      have hl : raw18920step0Labels = raw18920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18920 raw18920Labels permutation346 hz
    mixedMoment B raw18920step0 raw18920step0Labels = mixedMoment B raw18920step1 raw18920step1Labels := by
      have ha : raw18920step1 = (fun i j => raw18920step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18920step1 raw18920step0; decide +kernel
      have hl : raw18920step1Labels = raw18920step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18920step0 raw18920step0Labels permutation36 permutation6
    _ = mixedMoment B node3985 node3985Labels := by rfl

def raw18921 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18921 raw18921Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw18921 raw18921Labels = mixedMoment B raw18921step0 raw18921step0Labels := by
      have ha : raw18921step0 = (fun i j => raw18921 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18921step0 raw18921; decide +kernel
      have hl : raw18921step0Labels = raw18921Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18921 raw18921Labels permutation153 permutation6
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw18922 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18922 raw18922Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw18922 raw18922Labels = mixedMoment B raw18922step0 raw18922step0Labels := by
      have ha : raw18922step0 = (fun i j => raw18922 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18922step0 raw18922; decide +kernel
      have hl : raw18922step0Labels = raw18922Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18922 raw18922Labels permutation155 permutation6
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw18923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18923 raw18923Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18923 raw18923Labels = mixedMoment B raw18923step0 raw18923step0Labels := by
      have hz : ∀ j, raw18923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18923step0 = (fun i j => raw18923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18923step0 raw18923; decide +kernel
      have hl : raw18923step0Labels = raw18923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18923 raw18923Labels permutation346 hz
    mixedMoment B raw18923step0 raw18923step0Labels = mixedMoment B raw18923step1 raw18923step1Labels := by
      have ha : raw18923step1 = (fun i j => raw18923step0 (permutation61 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18923step1 raw18923step0; decide +kernel
      have hl : raw18923step1Labels = raw18923step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18923step0 raw18923step0Labels permutation61 permutation2
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw18924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18924step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18924step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18924 raw18924Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw18924 raw18924Labels = mixedMoment B raw18924step0 raw18924step0Labels := by
      have ha : raw18924step0 = (fun i j => raw18924 (permutation497 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18924step0 raw18924; decide +kernel
      have hl : raw18924step0Labels = raw18924Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18924 raw18924Labels permutation497 permutation7
    mixedMoment B raw18924step0 raw18924step0Labels = mixedMoment B raw18924step1 raw18924step1Labels := by
      have ha : raw18924step1 = raw18924step0 := by apply Matrix.ext; unfold raw18924step1 raw18924step0; decide +kernel
      have hl : raw18924step0Labels = labelEmbedding10 ∘ raw18924step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18924step0 raw18924step0Labels raw18924step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw18925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18925step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18925step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18925 raw18925Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18925 raw18925Labels = mixedMoment B raw18925step0 raw18925step0Labels := by
      have hz : ∀ j, raw18925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18925step0 = (fun i j => raw18925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18925step0 raw18925; decide +kernel
      have hl : raw18925step0Labels = raw18925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18925 raw18925Labels permutation346 hz
    mixedMoment B raw18925step0 raw18925step0Labels = mixedMoment B raw18925step1 raw18925step1Labels := by
      have ha : raw18925step1 = (fun i j => raw18925step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18925step1 raw18925step0; decide +kernel
      have hl : raw18925step1Labels = raw18925step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18925step0 raw18925step0Labels permutation92 permutation6
    mixedMoment B raw18925step1 raw18925step1Labels = mixedMoment B raw18925step2 raw18925step2Labels := by
      have ha : raw18925step2 = raw18925step1 := by apply Matrix.ext; unfold raw18925step2 raw18925step1; decide +kernel
      have hl : raw18925step1Labels = labelEmbedding9 ∘ raw18925step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18925step1 raw18925step1Labels raw18925step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18926step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18926step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18926step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18926 raw18926Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18926 raw18926Labels = mixedMoment B raw18926step0 raw18926step0Labels := by
      have hz : ∀ j, raw18926 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18926step0 = (fun i j => raw18926 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18926step0 raw18926; decide +kernel
      have hl : raw18926step0Labels = raw18926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18926 raw18926Labels permutation346 hz
    mixedMoment B raw18926step0 raw18926step0Labels = mixedMoment B raw18926step1 raw18926step1Labels := by
      have ha : raw18926step1 = (fun i j => raw18926step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18926step1 raw18926step0; decide +kernel
      have hl : raw18926step1Labels = raw18926step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18926step0 raw18926step0Labels permutation92 permutation6
    mixedMoment B raw18926step1 raw18926step1Labels = mixedMoment B raw18926step2 raw18926step2Labels := by
      have ha : raw18926step2 = raw18926step1 := by apply Matrix.ext; unfold raw18926step2 raw18926step1; decide +kernel
      have hl : raw18926step1Labels = labelEmbedding9 ∘ raw18926step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18926step1 raw18926step1Labels raw18926step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw18927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18927step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18927 raw18927Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw18927 raw18927Labels = mixedMoment B raw18927step0 raw18927step0Labels := by
      have hz : ∀ j, raw18927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18927step0 = (fun i j => raw18927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18927step0 raw18927; decide +kernel
      have hl : raw18927step0Labels = raw18927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18927 raw18927Labels permutation346 hz
    mixedMoment B raw18927step0 raw18927step0Labels = mixedMoment B raw18927step1 raw18927step1Labels := by
      have ha : raw18927step1 = (fun i j => raw18927step0 (permutation96 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18927step1 raw18927step0; decide +kernel
      have hl : raw18927step1Labels = raw18927step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18927step0 raw18927step0Labels permutation96 permutation7
    mixedMoment B raw18927step1 raw18927step1Labels = mixedMoment B raw18927step2 raw18927step2Labels := by
      have ha : raw18927step2 = raw18927step1 := by apply Matrix.ext; unfold raw18927step2 raw18927step1; decide +kernel
      have hl : raw18927step1Labels = labelEmbedding10 ∘ raw18927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18927step1 raw18927step1Labels raw18927step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw18928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18928step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18928step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18928 raw18928Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw18928 raw18928Labels = mixedMoment B raw18928step0 raw18928step0Labels := by
      have hz : ∀ j, raw18928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18928step0 = (fun i j => raw18928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18928step0 raw18928; decide +kernel
      have hl : raw18928step0Labels = raw18928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18928 raw18928Labels permutation346 hz
    mixedMoment B raw18928step0 raw18928step0Labels = mixedMoment B raw18928step1 raw18928step1Labels := by
      have ha : raw18928step1 = (fun i j => raw18928step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18928step1 raw18928step0; decide +kernel
      have hl : raw18928step1Labels = raw18928step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18928step0 raw18928step0Labels permutation32 permutation3
    mixedMoment B raw18928step1 raw18928step1Labels = mixedMoment B raw18928step2 raw18928step2Labels := by
      have ha : raw18928step2 = raw18928step1 := by apply Matrix.ext; unfold raw18928step2 raw18928step1; decide +kernel
      have hl : raw18928step1Labels = labelEmbedding6 ∘ raw18928step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18928step1 raw18928step1Labels raw18928step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw18929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18929step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18929 raw18929Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw18929 raw18929Labels = mixedMoment B raw18929step0 raw18929step0Labels := by
      have ha : raw18929step0 = (fun i j => raw18929 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18929step0 raw18929; decide +kernel
      have hl : raw18929step0Labels = raw18929Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18929 raw18929Labels permutation176 permutation3
    mixedMoment B raw18929step0 raw18929step0Labels = mixedMoment B raw18929step1 raw18929step1Labels := by
      have ha : raw18929step1 = raw18929step0 := by apply Matrix.ext; unfold raw18929step1 raw18929step0; decide +kernel
      have hl : raw18929step0Labels = labelEmbedding6 ∘ raw18929step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18929step0 raw18929step0Labels raw18929step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw18930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18930step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18930step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18930 raw18930Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18930 raw18930Labels = mixedMoment B raw18930step0 raw18930step0Labels := by
      have hz : ∀ j, raw18930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18930step0 = (fun i j => raw18930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18930step0 raw18930; decide +kernel
      have hl : raw18930step0Labels = raw18930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18930 raw18930Labels permutation346 hz
    mixedMoment B raw18930step0 raw18930step0Labels = mixedMoment B raw18930step1 raw18930step1Labels := by
      have ha : raw18930step1 = (fun i j => raw18930step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18930step1 raw18930step0; decide +kernel
      have hl : raw18930step1Labels = raw18930step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18930step0 raw18930step0Labels permutation92 permutation6
    mixedMoment B raw18930step1 raw18930step1Labels = mixedMoment B raw18930step2 raw18930step2Labels := by
      have ha : raw18930step2 = raw18930step1 := by apply Matrix.ext; unfold raw18930step2 raw18930step1; decide +kernel
      have hl : raw18930step1Labels = labelEmbedding9 ∘ raw18930step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18930step1 raw18930step1Labels raw18930step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw18931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18931step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18931step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18931 raw18931Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18931 raw18931Labels = mixedMoment B raw18931step0 raw18931step0Labels := by
      have hz : ∀ j, raw18931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18931step0 = (fun i j => raw18931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18931step0 raw18931; decide +kernel
      have hl : raw18931step0Labels = raw18931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18931 raw18931Labels permutation346 hz
    mixedMoment B raw18931step0 raw18931step0Labels = mixedMoment B raw18931step1 raw18931step1Labels := by
      have ha : raw18931step1 = (fun i j => raw18931step0 (permutation135 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18931step1 raw18931step0; decide +kernel
      have hl : raw18931step1Labels = raw18931step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18931step0 raw18931step0Labels permutation135 permutation4
    mixedMoment B raw18931step1 raw18931step1Labels = mixedMoment B raw18931step2 raw18931step2Labels := by
      have ha : raw18931step2 = raw18931step1 := by apply Matrix.ext; unfold raw18931step2 raw18931step1; decide +kernel
      have hl : raw18931step1Labels = labelEmbedding7 ∘ raw18931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18931step1 raw18931step1Labels raw18931step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw18932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18932step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18932 raw18932Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18932 raw18932Labels = mixedMoment B raw18932step0 raw18932step0Labels := by
      have hz : ∀ j, raw18932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18932step0 = (fun i j => raw18932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18932step0 raw18932; decide +kernel
      have hl : raw18932step0Labels = raw18932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18932 raw18932Labels permutation346 hz
    mixedMoment B raw18932step0 raw18932step0Labels = mixedMoment B raw18932step1 raw18932step1Labels := by
      have ha : raw18932step1 = (fun i j => raw18932step0 (permutation95 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18932step1 raw18932step0; decide +kernel
      have hl : raw18932step1Labels = raw18932step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18932step0 raw18932step0Labels permutation95 permutation7
    mixedMoment B raw18932step1 raw18932step1Labels = mixedMoment B raw18932step2 raw18932step2Labels := by
      have ha : raw18932step2 = raw18932step1 := by apply Matrix.ext; unfold raw18932step2 raw18932step1; decide +kernel
      have hl : raw18932step1Labels = labelEmbedding10 ∘ raw18932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18932step1 raw18932step1Labels raw18932step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw18933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18933step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18933 raw18933Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw18933 raw18933Labels = mixedMoment B raw18933step0 raw18933step0Labels := by
      have ha : raw18933step0 = (fun i j => raw18933 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18933step0 raw18933; decide +kernel
      have hl : raw18933step0Labels = raw18933Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18933 raw18933Labels permutation160 permutation3
    mixedMoment B raw18933step0 raw18933step0Labels = mixedMoment B raw18933step1 raw18933step1Labels := by
      have ha : raw18933step1 = raw18933step0 := by apply Matrix.ext; unfold raw18933step1 raw18933step0; decide +kernel
      have hl : raw18933step0Labels = labelEmbedding6 ∘ raw18933step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18933step0 raw18933step0Labels raw18933step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw18934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18934 raw18934Labels = mixedMoment B node5461 node5461Labels := by
  calc
    mixedMoment B raw18934 raw18934Labels = mixedMoment B raw18934step0 raw18934step0Labels := by
      have ha : raw18934step0 = (fun i j => raw18934 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18934step0 raw18934; decide +kernel
      have hl : raw18934step0Labels = raw18934Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18934 raw18934Labels permutation171 permutation2
    _ = mixedMoment B node5461 node5461Labels := by rfl

def raw18935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18935step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18935 raw18935Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18935 raw18935Labels = mixedMoment B raw18935step0 raw18935step0Labels := by
      have ha : raw18935step0 = (fun i j => raw18935 (permutation495 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18935step0 raw18935; decide +kernel
      have hl : raw18935step0Labels = raw18935Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18935 raw18935Labels permutation495 permutation6
    mixedMoment B raw18935step0 raw18935step0Labels = mixedMoment B raw18935step1 raw18935step1Labels := by
      have ha : raw18935step1 = raw18935step0 := by apply Matrix.ext; unfold raw18935step1 raw18935step0; decide +kernel
      have hl : raw18935step0Labels = labelEmbedding9 ∘ raw18935step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18935step0 raw18935step0Labels raw18935step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18936 raw18936Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw18936 raw18936Labels = mixedMoment B raw18936step0 raw18936step0Labels := by
      have ha : raw18936step0 = (fun i j => raw18936 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18936step0 raw18936; decide +kernel
      have hl : raw18936step0Labels = raw18936Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18936 raw18936Labels permutation168 permutation2
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw18937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18937 raw18937Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw18937 raw18937Labels = mixedMoment B raw18937step0 raw18937step0Labels := by
      have ha : raw18937step0 = (fun i j => raw18937 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18937step0 raw18937; decide +kernel
      have hl : raw18937step0Labels = raw18937Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18937 raw18937Labels permutation171 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw18938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18938step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18938 raw18938Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw18938 raw18938Labels = mixedMoment B raw18938step0 raw18938step0Labels := by
      have hz : ∀ j, raw18938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18938step0 = (fun i j => raw18938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18938step0 raw18938; decide +kernel
      have hl : raw18938step0Labels = raw18938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18938 raw18938Labels permutation346 hz
    mixedMoment B raw18938step0 raw18938step0Labels = mixedMoment B raw18938step1 raw18938step1Labels := by
      have ha : raw18938step1 = (fun i j => raw18938step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18938step1 raw18938step0; decide +kernel
      have hl : raw18938step1Labels = raw18938step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18938step0 raw18938step0Labels permutation35 permutation3
    mixedMoment B raw18938step1 raw18938step1Labels = mixedMoment B raw18938step2 raw18938step2Labels := by
      have ha : raw18938step2 = raw18938step1 := by apply Matrix.ext; unfold raw18938step2 raw18938step1; decide +kernel
      have hl : raw18938step1Labels = labelEmbedding6 ∘ raw18938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18938step1 raw18938step1Labels raw18938step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw18939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18939 raw18939Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw18939 raw18939Labels = mixedMoment B raw18939step0 raw18939step0Labels := by
      have hz : ∀ j, raw18939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18939step0 = (fun i j => raw18939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18939step0 raw18939; decide +kernel
      have hl : raw18939step0Labels = raw18939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18939 raw18939Labels permutation346 hz
    mixedMoment B raw18939step0 raw18939step0Labels = mixedMoment B raw18939step1 raw18939step1Labels := by
      have ha : raw18939step1 = (fun i j => raw18939step0 (permutation96 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18939step1 raw18939step0; decide +kernel
      have hl : raw18939step1Labels = raw18939step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18939step0 raw18939step0Labels permutation96 permutation2
    mixedMoment B raw18939step1 raw18939step1Labels = mixedMoment B raw18939step2 raw18939step2Labels := by
      have ha : raw18939step2 = -raw18939step1 := by apply Matrix.ext; change ∀ i j, raw18939step2 i j = -(raw18939step1 i j); unfold raw18939step2 raw18939step1; decide +kernel
      have hl : raw18939step2Labels = raw18939step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw18940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18940step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18940 raw18940Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18940 raw18940Labels = mixedMoment B raw18940step0 raw18940step0Labels := by
      have ha : raw18940step0 = (fun i j => raw18940 (permutation504 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18940step0 raw18940; decide +kernel
      have hl : raw18940step0Labels = raw18940Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18940 raw18940Labels permutation504 permutation2
    mixedMoment B raw18940step0 raw18940step0Labels = mixedMoment B raw18940step1 raw18940step1Labels := by
      have ha : raw18940step1 = -raw18940step0 := by apply Matrix.ext; change ∀ i j, raw18940step1 i j = -(raw18940step0 i j); unfold raw18940step1 raw18940step0; decide +kernel
      have hl : raw18940step1Labels = raw18940step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw18941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18941step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18941step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18941 raw18941Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18941 raw18941Labels = mixedMoment B raw18941step0 raw18941step0Labels := by
      have hz : ∀ j, raw18941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18941step0 = (fun i j => raw18941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18941step0 raw18941; decide +kernel
      have hl : raw18941step0Labels = raw18941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18941 raw18941Labels permutation346 hz
    mixedMoment B raw18941step0 raw18941step0Labels = mixedMoment B raw18941step1 raw18941step1Labels := by
      have ha : raw18941step1 = (fun i j => raw18941step0 (permutation97 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18941step1 raw18941step0; decide +kernel
      have hl : raw18941step1Labels = raw18941step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18941step0 raw18941step0Labels permutation97 permutation7
    mixedMoment B raw18941step1 raw18941step1Labels = mixedMoment B raw18941step2 raw18941step2Labels := by
      have ha : raw18941step2 = raw18941step1 := by apply Matrix.ext; unfold raw18941step2 raw18941step1; decide +kernel
      have hl : raw18941step1Labels = labelEmbedding10 ∘ raw18941step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18941step1 raw18941step1Labels raw18941step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw18942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18942step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18942 raw18942Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw18942 raw18942Labels = mixedMoment B raw18942step0 raw18942step0Labels := by
      have hz : ∀ j, raw18942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18942step0 = (fun i j => raw18942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18942step0 raw18942; decide +kernel
      have hl : raw18942step0Labels = raw18942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18942 raw18942Labels permutation346 hz
    mixedMoment B raw18942step0 raw18942step0Labels = mixedMoment B raw18942step1 raw18942step1Labels := by
      have ha : raw18942step1 = (fun i j => raw18942step0 (permutation97 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18942step1 raw18942step0; decide +kernel
      have hl : raw18942step1Labels = raw18942step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18942step0 raw18942step0Labels permutation97 permutation2
    mixedMoment B raw18942step1 raw18942step1Labels = mixedMoment B raw18942step2 raw18942step2Labels := by
      have ha : raw18942step2 = -raw18942step1 := by apply Matrix.ext; change ∀ i j, raw18942step2 i j = -(raw18942step1 i j); unfold raw18942step2 raw18942step1; decide +kernel
      have hl : raw18942step2Labels = raw18942step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw18943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18943step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18943step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18943 raw18943Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw18943 raw18943Labels = mixedMoment B raw18943step0 raw18943step0Labels := by
      have hz : ∀ j, raw18943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18943step0 = (fun i j => raw18943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18943step0 raw18943; decide +kernel
      have hl : raw18943step0Labels = raw18943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18943 raw18943Labels permutation346 hz
    mixedMoment B raw18943step0 raw18943step0Labels = mixedMoment B raw18943step1 raw18943step1Labels := by
      have ha : raw18943step1 = (fun i j => raw18943step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18943step1 raw18943step0; decide +kernel
      have hl : raw18943step1Labels = raw18943step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18943step0 raw18943step0Labels permutation33 permutation3
    mixedMoment B raw18943step1 raw18943step1Labels = mixedMoment B raw18943step2 raw18943step2Labels := by
      have ha : raw18943step2 = raw18943step1 := by apply Matrix.ext; unfold raw18943step2 raw18943step1; decide +kernel
      have hl : raw18943step1Labels = labelEmbedding6 ∘ raw18943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18943step1 raw18943step1Labels raw18943step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
