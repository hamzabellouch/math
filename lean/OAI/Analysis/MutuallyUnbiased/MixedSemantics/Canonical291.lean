import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37248step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37248 raw37248Labels = mixedMoment B node5372 node5372Labels := by
  calc
    mixedMoment B raw37248 raw37248Labels = mixedMoment B raw37248step0 raw37248step0Labels := by
      have ha : raw37248step0 = (fun i j => raw37248 (permutation347 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37248step0 raw37248; decide +kernel
      have hl : raw37248step0Labels = raw37248Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37248 raw37248Labels permutation347 permutation3
    mixedMoment B raw37248step0 raw37248step0Labels = mixedMoment B raw37248step1 raw37248step1Labels := by
      have ha : raw37248step1 = raw37248step0 := by apply Matrix.ext; unfold raw37248step1 raw37248step0; decide +kernel
      have hl : raw37248step0Labels = labelEmbedding6 ∘ raw37248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37248step0 raw37248step0Labels raw37248step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5372 node5372Labels := by rfl

def raw37249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw37249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw37249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37249 raw37249Labels = mixedMoment B node5114 node5114Labels := by
  calc
    mixedMoment B raw37249 raw37249Labels = mixedMoment B raw37249step0 raw37249step0Labels := by
      have ha : raw37249step0 = (fun i j => raw37249 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37249step0 raw37249; decide +kernel
      have hl : raw37249step0Labels = raw37249Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37249 raw37249Labels permutation662 permutation2
    mixedMoment B raw37249step0 raw37249step0Labels = mixedMoment B raw37249step1 raw37249step1Labels := by
      have ha : raw37249step1 = -raw37249step0 := by apply Matrix.ext; change ∀ i j, raw37249step1 i j = -(raw37249step0 i j); unfold raw37249step1 raw37249step0; decide +kernel
      have hl : raw37249step1Labels = raw37249step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5114 node5114Labels := by rfl

def raw37250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw37250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw37250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw37250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37250 raw37250Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw37250 raw37250Labels = mixedMoment B raw37250step0 raw37250step0Labels := by
      have hz : ∀ j, raw37250 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37250step0 = (fun i j => raw37250 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37250step0 raw37250; decide +kernel
      have hl : raw37250step0Labels = raw37250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37250 raw37250Labels permutation520 hz
    mixedMoment B raw37250step0 raw37250step0Labels = mixedMoment B raw37250step1 raw37250step1Labels := by
      have ha : raw37250step1 = (fun i j => raw37250step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37250step1 raw37250step0; decide +kernel
      have hl : raw37250step1Labels = raw37250step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37250step0 raw37250step0Labels permutation149 permutation2
    mixedMoment B raw37250step1 raw37250step1Labels = mixedMoment B raw37250step2 raw37250step2Labels := by
      have ha : raw37250step2 = -raw37250step1 := by apply Matrix.ext; change ∀ i j, raw37250step2 i j = -(raw37250step1 i j); unfold raw37250step2 raw37250step1; decide +kernel
      have hl : raw37250step2Labels = raw37250step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw37251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw37251step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37251step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37251step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37251step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37251 raw37251Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw37251 raw37251Labels = mixedMoment B raw37251step0 raw37251step0Labels := by
      have ha : raw37251step0 = (fun i j => raw37251 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37251step0 raw37251; decide +kernel
      have hl : raw37251step0Labels = raw37251Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37251 raw37251Labels permutation663 permutation3
    mixedMoment B raw37251step0 raw37251step0Labels = mixedMoment B raw37251step1 raw37251step1Labels := by
      have ha : raw37251step1 = -raw37251step0 := by apply Matrix.ext; change ∀ i j, raw37251step1 i j = -(raw37251step0 i j); unfold raw37251step1 raw37251step0; decide +kernel
      have hl : raw37251step1Labels = raw37251step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37251step1 raw37251step1Labels = mixedMoment B raw37251step2 raw37251step2Labels := by
      have ha : raw37251step2 = raw37251step1 := by apply Matrix.ext; unfold raw37251step2 raw37251step1; decide +kernel
      have hl : raw37251step1Labels = labelEmbedding6 ∘ raw37251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37251step1 raw37251step1Labels raw37251step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw37252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw37252step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37252step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37252 raw37252Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw37252 raw37252Labels = mixedMoment B raw37252step0 raw37252step0Labels := by
      have ha : raw37252step0 = (fun i j => raw37252 (permutation661 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37252step0 raw37252; decide +kernel
      have hl : raw37252step0Labels = raw37252Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37252 raw37252Labels permutation661 permutation3
    mixedMoment B raw37252step0 raw37252step0Labels = mixedMoment B raw37252step1 raw37252step1Labels := by
      have ha : raw37252step1 = -raw37252step0 := by apply Matrix.ext; change ∀ i j, raw37252step1 i j = -(raw37252step0 i j); unfold raw37252step1 raw37252step0; decide +kernel
      have hl : raw37252step1Labels = raw37252step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37252step1 raw37252step1Labels = mixedMoment B raw37252step2 raw37252step2Labels := by
      have ha : raw37252step2 = raw37252step1 := by apply Matrix.ext; unfold raw37252step2 raw37252step1; decide +kernel
      have hl : raw37252step1Labels = labelEmbedding6 ∘ raw37252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37252step1 raw37252step1Labels raw37252step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw37253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw37253step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37253step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37253step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37253step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37253 raw37253Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw37253 raw37253Labels = mixedMoment B raw37253step0 raw37253step0Labels := by
      have ha : raw37253step0 = (fun i j => raw37253 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37253step0 raw37253; decide +kernel
      have hl : raw37253step0Labels = raw37253Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37253 raw37253Labels permutation662 permutation3
    mixedMoment B raw37253step0 raw37253step0Labels = mixedMoment B raw37253step1 raw37253step1Labels := by
      have ha : raw37253step1 = -raw37253step0 := by apply Matrix.ext; change ∀ i j, raw37253step1 i j = -(raw37253step0 i j); unfold raw37253step1 raw37253step0; decide +kernel
      have hl : raw37253step1Labels = raw37253step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37253step1 raw37253step1Labels = mixedMoment B raw37253step2 raw37253step2Labels := by
      have ha : raw37253step2 = raw37253step1 := by apply Matrix.ext; unfold raw37253step2 raw37253step1; decide +kernel
      have hl : raw37253step1Labels = labelEmbedding6 ∘ raw37253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37253step1 raw37253step1Labels raw37253step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw37254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37254step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37254 raw37254Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw37254 raw37254Labels = mixedMoment B raw37254step0 raw37254step0Labels := by
      have ha : raw37254step0 = (fun i j => raw37254 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37254step0 raw37254; decide +kernel
      have hl : raw37254step0Labels = raw37254Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37254 raw37254Labels permutation176 permutation3
    mixedMoment B raw37254step0 raw37254step0Labels = mixedMoment B raw37254step1 raw37254step1Labels := by
      have ha : raw37254step1 = raw37254step0 := by apply Matrix.ext; unfold raw37254step1 raw37254step0; decide +kernel
      have hl : raw37254step0Labels = labelEmbedding6 ∘ raw37254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37254step0 raw37254step0Labels raw37254step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw37255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37255step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37255 raw37255Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw37255 raw37255Labels = mixedMoment B raw37255step0 raw37255step0Labels := by
      have ha : raw37255step0 = (fun i j => raw37255 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37255step0 raw37255; decide +kernel
      have hl : raw37255step0Labels = raw37255Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37255 raw37255Labels permutation188 permutation3
    mixedMoment B raw37255step0 raw37255step0Labels = mixedMoment B raw37255step1 raw37255step1Labels := by
      have ha : raw37255step1 = raw37255step0 := by apply Matrix.ext; unfold raw37255step1 raw37255step0; decide +kernel
      have hl : raw37255step0Labels = labelEmbedding6 ∘ raw37255step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37255step0 raw37255step0Labels raw37255step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw37256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37256step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37256step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37256 raw37256Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw37256 raw37256Labels = mixedMoment B raw37256step0 raw37256step0Labels := by
      have ha : raw37256step0 = (fun i j => raw37256 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37256step0 raw37256; decide +kernel
      have hl : raw37256step0Labels = raw37256Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37256 raw37256Labels permutation154 permutation3
    mixedMoment B raw37256step0 raw37256step0Labels = mixedMoment B raw37256step1 raw37256step1Labels := by
      have ha : raw37256step1 = raw37256step0 := by apply Matrix.ext; unfold raw37256step1 raw37256step0; decide +kernel
      have hl : raw37256step0Labels = labelEmbedding6 ∘ raw37256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37256step0 raw37256step0Labels raw37256step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

def raw37257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37257step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37257 raw37257Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw37257 raw37257Labels = mixedMoment B raw37257step0 raw37257step0Labels := by
      have ha : raw37257step0 = (fun i j => raw37257 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37257step0 raw37257; decide +kernel
      have hl : raw37257step0Labels = raw37257Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37257 raw37257Labels permutation178 permutation3
    mixedMoment B raw37257step0 raw37257step0Labels = mixedMoment B raw37257step1 raw37257step1Labels := by
      have ha : raw37257step1 = raw37257step0 := by apply Matrix.ext; unfold raw37257step1 raw37257step0; decide +kernel
      have hl : raw37257step0Labels = labelEmbedding6 ∘ raw37257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37257step0 raw37257step0Labels raw37257step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

def raw37258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw37258step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37258step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37258step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37258 raw37258Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw37258 raw37258Labels = mixedMoment B raw37258step0 raw37258step0Labels := by
      have ha : raw37258step0 = (fun i j => raw37258 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37258step0 raw37258; decide +kernel
      have hl : raw37258step0Labels = raw37258Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37258 raw37258Labels permutation662 permutation3
    mixedMoment B raw37258step0 raw37258step0Labels = mixedMoment B raw37258step1 raw37258step1Labels := by
      have ha : raw37258step1 = -raw37258step0 := by apply Matrix.ext; change ∀ i j, raw37258step1 i j = -(raw37258step0 i j); unfold raw37258step1 raw37258step0; decide +kernel
      have hl : raw37258step1Labels = raw37258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37258step1 raw37258step1Labels = mixedMoment B raw37258step2 raw37258step2Labels := by
      have ha : raw37258step2 = raw37258step1 := by apply Matrix.ext; unfold raw37258step2 raw37258step1; decide +kernel
      have hl : raw37258step1Labels = labelEmbedding6 ∘ raw37258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37258step1 raw37258step1Labels raw37258step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw37259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw37259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37259step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37259 raw37259Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw37259 raw37259Labels = mixedMoment B raw37259step0 raw37259step0Labels := by
      have ha : raw37259step0 = (fun i j => raw37259 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37259step0 raw37259; decide +kernel
      have hl : raw37259step0Labels = raw37259Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37259 raw37259Labels permutation152 permutation3
    mixedMoment B raw37259step0 raw37259step0Labels = mixedMoment B raw37259step1 raw37259step1Labels := by
      have ha : raw37259step1 = raw37259step0 := by apply Matrix.ext; unfold raw37259step1 raw37259step0; decide +kernel
      have hl : raw37259step0Labels = labelEmbedding6 ∘ raw37259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37259step0 raw37259step0Labels raw37259step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

def raw37260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw37260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37260step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37260 raw37260Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw37260 raw37260Labels = mixedMoment B raw37260step0 raw37260step0Labels := by
      have ha : raw37260step0 = (fun i j => raw37260 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37260step0 raw37260; decide +kernel
      have hl : raw37260step0Labels = raw37260Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37260 raw37260Labels permutation176 permutation3
    mixedMoment B raw37260step0 raw37260step0Labels = mixedMoment B raw37260step1 raw37260step1Labels := by
      have ha : raw37260step1 = raw37260step0 := by apply Matrix.ext; unfold raw37260step1 raw37260step0; decide +kernel
      have hl : raw37260step0Labels = labelEmbedding6 ∘ raw37260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37260step0 raw37260step0Labels raw37260step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

def raw37261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw37261step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37261step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37261step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37261 raw37261Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw37261 raw37261Labels = mixedMoment B raw37261step0 raw37261step0Labels := by
      have ha : raw37261step0 = (fun i j => raw37261 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37261step0 raw37261; decide +kernel
      have hl : raw37261step0Labels = raw37261Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37261 raw37261Labels permutation664 permutation3
    mixedMoment B raw37261step0 raw37261step0Labels = mixedMoment B raw37261step1 raw37261step1Labels := by
      have ha : raw37261step1 = -raw37261step0 := by apply Matrix.ext; change ∀ i j, raw37261step1 i j = -(raw37261step0 i j); unfold raw37261step1 raw37261step0; decide +kernel
      have hl : raw37261step1Labels = raw37261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37261step1 raw37261step1Labels = mixedMoment B raw37261step2 raw37261step2Labels := by
      have ha : raw37261step2 = raw37261step1 := by apply Matrix.ext; unfold raw37261step2 raw37261step1; decide +kernel
      have hl : raw37261step1Labels = labelEmbedding6 ∘ raw37261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37261step1 raw37261step1Labels raw37261step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

def raw37262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw37262step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37262step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37262step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37262 raw37262Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw37262 raw37262Labels = mixedMoment B raw37262step0 raw37262step0Labels := by
      have ha : raw37262step0 = (fun i j => raw37262 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37262step0 raw37262; decide +kernel
      have hl : raw37262step0Labels = raw37262Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37262 raw37262Labels permutation662 permutation3
    mixedMoment B raw37262step0 raw37262step0Labels = mixedMoment B raw37262step1 raw37262step1Labels := by
      have ha : raw37262step1 = -raw37262step0 := by apply Matrix.ext; change ∀ i j, raw37262step1 i j = -(raw37262step0 i j); unfold raw37262step1 raw37262step0; decide +kernel
      have hl : raw37262step1Labels = raw37262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37262step1 raw37262step1Labels = mixedMoment B raw37262step2 raw37262step2Labels := by
      have ha : raw37262step2 = raw37262step1 := by apply Matrix.ext; unfold raw37262step2 raw37262step1; decide +kernel
      have hl : raw37262step1Labels = labelEmbedding6 ∘ raw37262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37262step1 raw37262step1Labels raw37262step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

def raw37263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw37263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw37263step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37263step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37263step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37263step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37263 raw37263Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw37263 raw37263Labels = mixedMoment B raw37263step0 raw37263step0Labels := by
      have ha : raw37263step0 = (fun i j => raw37263 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37263step0 raw37263; decide +kernel
      have hl : raw37263step0Labels = raw37263Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37263 raw37263Labels permutation662 permutation3
    mixedMoment B raw37263step0 raw37263step0Labels = mixedMoment B raw37263step1 raw37263step1Labels := by
      have ha : raw37263step1 = -raw37263step0 := by apply Matrix.ext; change ∀ i j, raw37263step1 i j = -(raw37263step0 i j); unfold raw37263step1 raw37263step0; decide +kernel
      have hl : raw37263step1Labels = raw37263step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37263step1 raw37263step1Labels = mixedMoment B raw37263step2 raw37263step2Labels := by
      have ha : raw37263step2 = raw37263step1 := by apply Matrix.ext; unfold raw37263step2 raw37263step1; decide +kernel
      have hl : raw37263step1Labels = labelEmbedding6 ∘ raw37263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37263step1 raw37263step1Labels raw37263step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw37264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw37264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37264 raw37264Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw37264 raw37264Labels = mixedMoment B raw37264step0 raw37264step0Labels := by
      have ha : raw37264step0 = (fun i j => raw37264 (permutation660 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37264step0 raw37264; decide +kernel
      have hl : raw37264step0Labels = raw37264Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37264 raw37264Labels permutation660 permutation2
    mixedMoment B raw37264step0 raw37264step0Labels = mixedMoment B raw37264step1 raw37264step1Labels := by
      have ha : raw37264step1 = -raw37264step0 := by apply Matrix.ext; change ∀ i j, raw37264step1 i j = -(raw37264step0 i j); unfold raw37264step1 raw37264step0; decide +kernel
      have hl : raw37264step1Labels = raw37264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw37265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw37265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37265 raw37265Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw37265 raw37265Labels = mixedMoment B raw37265step0 raw37265step0Labels := by
      have ha : raw37265step0 = (fun i j => raw37265 (permutation659 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37265step0 raw37265; decide +kernel
      have hl : raw37265step0Labels = raw37265Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37265 raw37265Labels permutation659 permutation2
    mixedMoment B raw37265step0 raw37265step0Labels = mixedMoment B raw37265step1 raw37265step1Labels := by
      have ha : raw37265step1 = -raw37265step0 := by apply Matrix.ext; change ∀ i j, raw37265step1 i j = -(raw37265step0 i j); unfold raw37265step1 raw37265step0; decide +kernel
      have hl : raw37265step1Labels = raw37265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw37266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37266step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37266 raw37266Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw37266 raw37266Labels = mixedMoment B raw37266step0 raw37266step0Labels := by
      have ha : raw37266step0 = (fun i j => raw37266 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37266step0 raw37266; decide +kernel
      have hl : raw37266step0Labels = raw37266Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37266 raw37266Labels permutation650 permutation7
    mixedMoment B raw37266step0 raw37266step0Labels = mixedMoment B raw37266step1 raw37266step1Labels := by
      have ha : raw37266step1 = raw37266step0 := by apply Matrix.ext; unfold raw37266step1 raw37266step0; decide +kernel
      have hl : raw37266step0Labels = labelEmbedding10 ∘ raw37266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37266step0 raw37266step0Labels raw37266step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw37267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37267 raw37267Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw37267 raw37267Labels = mixedMoment B raw37267step0 raw37267step0Labels := by
      have ha : raw37267step0 = (fun i j => raw37267 (permutation659 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37267step0 raw37267; decide +kernel
      have hl : raw37267step0Labels = raw37267Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37267 raw37267Labels permutation659 permutation2
    mixedMoment B raw37267step0 raw37267step0Labels = mixedMoment B raw37267step1 raw37267step1Labels := by
      have ha : raw37267step1 = -raw37267step0 := by apply Matrix.ext; change ∀ i j, raw37267step1 i j = -(raw37267step0 i j); unfold raw37267step1 raw37267step0; decide +kernel
      have hl : raw37267step1Labels = raw37267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw37268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37268step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37268 raw37268Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw37268 raw37268Labels = mixedMoment B raw37268step0 raw37268step0Labels := by
      have ha : raw37268step0 = (fun i j => raw37268 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37268step0 raw37268; decide +kernel
      have hl : raw37268step0Labels = raw37268Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37268 raw37268Labels permutation650 permutation7
    mixedMoment B raw37268step0 raw37268step0Labels = mixedMoment B raw37268step1 raw37268step1Labels := by
      have ha : raw37268step1 = raw37268step0 := by apply Matrix.ext; unfold raw37268step1 raw37268step0; decide +kernel
      have hl : raw37268step0Labels = labelEmbedding10 ∘ raw37268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37268step0 raw37268step0Labels raw37268step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw37269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37269step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37269step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37269 raw37269Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw37269 raw37269Labels = mixedMoment B raw37269step0 raw37269step0Labels := by
      have ha : raw37269step0 = (fun i j => raw37269 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37269step0 raw37269; decide +kernel
      have hl : raw37269step0Labels = raw37269Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37269 raw37269Labels permutation176 permutation3
    mixedMoment B raw37269step0 raw37269step0Labels = mixedMoment B raw37269step1 raw37269step1Labels := by
      have ha : raw37269step1 = raw37269step0 := by apply Matrix.ext; unfold raw37269step1 raw37269step0; decide +kernel
      have hl : raw37269step0Labels = labelEmbedding6 ∘ raw37269step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37269step0 raw37269step0Labels raw37269step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw37270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37270step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37270 raw37270Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw37270 raw37270Labels = mixedMoment B raw37270step0 raw37270step0Labels := by
      have ha : raw37270step0 = (fun i j => raw37270 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37270step0 raw37270; decide +kernel
      have hl : raw37270step0Labels = raw37270Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37270 raw37270Labels permutation176 permutation3
    mixedMoment B raw37270step0 raw37270step0Labels = mixedMoment B raw37270step1 raw37270step1Labels := by
      have ha : raw37270step1 = raw37270step0 := by apply Matrix.ext; unfold raw37270step1 raw37270step0; decide +kernel
      have hl : raw37270step0Labels = labelEmbedding6 ∘ raw37270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37270step0 raw37270step0Labels raw37270step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw37271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37271step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37271 raw37271Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw37271 raw37271Labels = mixedMoment B raw37271step0 raw37271step0Labels := by
      have ha : raw37271step0 = (fun i j => raw37271 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37271step0 raw37271; decide +kernel
      have hl : raw37271step0Labels = raw37271Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37271 raw37271Labels permutation182 permutation3
    mixedMoment B raw37271step0 raw37271step0Labels = mixedMoment B raw37271step1 raw37271step1Labels := by
      have ha : raw37271step1 = raw37271step0 := by apply Matrix.ext; unfold raw37271step1 raw37271step0; decide +kernel
      have hl : raw37271step0Labels = labelEmbedding6 ∘ raw37271step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37271step0 raw37271step0Labels raw37271step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw37272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37272 raw37272Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw37272 raw37272Labels = mixedMoment B raw37272step0 raw37272step0Labels := by
      have ha : raw37272step0 = (fun i j => raw37272 (permutation654 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37272step0 raw37272; decide +kernel
      have hl : raw37272step0Labels = raw37272Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37272 raw37272Labels permutation654 permutation2
    mixedMoment B raw37272step0 raw37272step0Labels = mixedMoment B raw37272step1 raw37272step1Labels := by
      have ha : raw37272step1 = -raw37272step0 := by apply Matrix.ext; change ∀ i j, raw37272step1 i j = -(raw37272step0 i j); unfold raw37272step1 raw37272step0; decide +kernel
      have hl : raw37272step1Labels = raw37272step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw37273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw37273step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37273step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw37273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37273 raw37273Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw37273 raw37273Labels = mixedMoment B raw37273step0 raw37273step0Labels := by
      have ha : raw37273step0 = (fun i j => raw37273 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37273step0 raw37273; decide +kernel
      have hl : raw37273step0Labels = raw37273Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37273 raw37273Labels permutation180 permutation3
    mixedMoment B raw37273step0 raw37273step0Labels = mixedMoment B raw37273step1 raw37273step1Labels := by
      have ha : raw37273step1 = raw37273step0 := by apply Matrix.ext; unfold raw37273step1 raw37273step0; decide +kernel
      have hl : raw37273step0Labels = labelEmbedding6 ∘ raw37273step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37273step0 raw37273step0Labels raw37273step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw37274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37274step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37274 raw37274Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw37274 raw37274Labels = mixedMoment B raw37274step0 raw37274step0Labels := by
      have ha : raw37274step0 = (fun i j => raw37274 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37274step0 raw37274; decide +kernel
      have hl : raw37274step0Labels = raw37274Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37274 raw37274Labels permutation152 permutation3
    mixedMoment B raw37274step0 raw37274step0Labels = mixedMoment B raw37274step1 raw37274step1Labels := by
      have ha : raw37274step1 = raw37274step0 := by apply Matrix.ext; unfold raw37274step1 raw37274step0; decide +kernel
      have hl : raw37274step0Labels = labelEmbedding6 ∘ raw37274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37274step0 raw37274step0Labels raw37274step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw37275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37275step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37275 raw37275Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw37275 raw37275Labels = mixedMoment B raw37275step0 raw37275step0Labels := by
      have ha : raw37275step0 = (fun i j => raw37275 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37275step0 raw37275; decide +kernel
      have hl : raw37275step0Labels = raw37275Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37275 raw37275Labels permutation152 permutation3
    mixedMoment B raw37275step0 raw37275step0Labels = mixedMoment B raw37275step1 raw37275step1Labels := by
      have ha : raw37275step1 = raw37275step0 := by apply Matrix.ext; unfold raw37275step1 raw37275step0; decide +kernel
      have hl : raw37275step0Labels = labelEmbedding6 ∘ raw37275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37275step0 raw37275step0Labels raw37275step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw37276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37276step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37276 raw37276Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw37276 raw37276Labels = mixedMoment B raw37276step0 raw37276step0Labels := by
      have ha : raw37276step0 = (fun i j => raw37276 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37276step0 raw37276; decide +kernel
      have hl : raw37276step0Labels = raw37276Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37276 raw37276Labels permutation158 permutation3
    mixedMoment B raw37276step0 raw37276step0Labels = mixedMoment B raw37276step1 raw37276step1Labels := by
      have ha : raw37276step1 = raw37276step0 := by apply Matrix.ext; unfold raw37276step1 raw37276step0; decide +kernel
      have hl : raw37276step0Labels = labelEmbedding6 ∘ raw37276step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37276step0 raw37276step0Labels raw37276step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw37277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37277 raw37277Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw37277 raw37277Labels = mixedMoment B raw37277step0 raw37277step0Labels := by
      have ha : raw37277step0 = (fun i j => raw37277 (permutation658 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37277step0 raw37277; decide +kernel
      have hl : raw37277step0Labels = raw37277Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37277 raw37277Labels permutation658 permutation2
    mixedMoment B raw37277step0 raw37277step0Labels = mixedMoment B raw37277step1 raw37277step1Labels := by
      have ha : raw37277step1 = -raw37277step0 := by apply Matrix.ext; change ∀ i j, raw37277step1 i j = -(raw37277step0 i j); unfold raw37277step1 raw37277step0; decide +kernel
      have hl : raw37277step1Labels = raw37277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw37278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw37278step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw37278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37278 raw37278Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw37278 raw37278Labels = mixedMoment B raw37278step0 raw37278step0Labels := by
      have ha : raw37278step0 = (fun i j => raw37278 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37278step0 raw37278; decide +kernel
      have hl : raw37278step0Labels = raw37278Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37278 raw37278Labels permutation156 permutation3
    mixedMoment B raw37278step0 raw37278step0Labels = mixedMoment B raw37278step1 raw37278step1Labels := by
      have ha : raw37278step1 = raw37278step0 := by apply Matrix.ext; unfold raw37278step1 raw37278step0; decide +kernel
      have hl : raw37278step0Labels = labelEmbedding6 ∘ raw37278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37278step0 raw37278step0Labels raw37278step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw37279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37279step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37279 raw37279Labels = mixedMoment B node4768 node4768Labels := by
  calc
    mixedMoment B raw37279 raw37279Labels = mixedMoment B raw37279step0 raw37279step0Labels := by
      have ha : raw37279step0 = (fun i j => raw37279 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37279step0 raw37279; decide +kernel
      have hl : raw37279step0Labels = raw37279Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37279 raw37279Labels permutation155 permutation3
    mixedMoment B raw37279step0 raw37279step0Labels = mixedMoment B raw37279step1 raw37279step1Labels := by
      have ha : raw37279step1 = raw37279step0 := by apply Matrix.ext; unfold raw37279step1 raw37279step0; decide +kernel
      have hl : raw37279step0Labels = labelEmbedding6 ∘ raw37279step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37279step0 raw37279step0Labels raw37279step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4768 node4768Labels := by rfl

def raw37280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37280step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37280 raw37280Labels = mixedMoment B node5338 node5338Labels := by
  calc
    mixedMoment B raw37280 raw37280Labels = mixedMoment B raw37280step0 raw37280step0Labels := by
      have ha : raw37280step0 = (fun i j => raw37280 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37280step0 raw37280; decide +kernel
      have hl : raw37280step0Labels = raw37280Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37280 raw37280Labels permutation155 permutation3
    mixedMoment B raw37280step0 raw37280step0Labels = mixedMoment B raw37280step1 raw37280step1Labels := by
      have ha : raw37280step1 = raw37280step0 := by apply Matrix.ext; unfold raw37280step1 raw37280step0; decide +kernel
      have hl : raw37280step0Labels = labelEmbedding6 ∘ raw37280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37280step0 raw37280step0Labels raw37280step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5338 node5338Labels := by rfl

def raw37281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37281step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37281 raw37281Labels = mixedMoment B node5338 node5338Labels := by
  calc
    mixedMoment B raw37281 raw37281Labels = mixedMoment B raw37281step0 raw37281step0Labels := by
      have ha : raw37281step0 = (fun i j => raw37281 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37281step0 raw37281; decide +kernel
      have hl : raw37281step0Labels = raw37281Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37281 raw37281Labels permutation179 permutation3
    mixedMoment B raw37281step0 raw37281step0Labels = mixedMoment B raw37281step1 raw37281step1Labels := by
      have ha : raw37281step1 = raw37281step0 := by apply Matrix.ext; unfold raw37281step1 raw37281step0; decide +kernel
      have hl : raw37281step0Labels = labelEmbedding6 ∘ raw37281step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37281step0 raw37281step0Labels raw37281step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5338 node5338Labels := by rfl

def raw37282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37282 raw37282Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw37282 raw37282Labels = mixedMoment B raw37282step0 raw37282step0Labels := by
      have ha : raw37282step0 = (fun i j => raw37282 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37282step0 raw37282; decide +kernel
      have hl : raw37282step0Labels = raw37282Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37282 raw37282Labels permutation662 permutation2
    mixedMoment B raw37282step0 raw37282step0Labels = mixedMoment B raw37282step1 raw37282step1Labels := by
      have ha : raw37282step1 = -raw37282step0 := by apply Matrix.ext; change ∀ i j, raw37282step1 i j = -(raw37282step0 i j); unfold raw37282step1 raw37282step0; decide +kernel
      have hl : raw37282step1Labels = raw37282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw37283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw37283step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw37283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37283 raw37283Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw37283 raw37283Labels = mixedMoment B raw37283step0 raw37283step0Labels := by
      have ha : raw37283step0 = (fun i j => raw37283 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37283step0 raw37283; decide +kernel
      have hl : raw37283step0Labels = raw37283Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37283 raw37283Labels permutation157 permutation3
    mixedMoment B raw37283step0 raw37283step0Labels = mixedMoment B raw37283step1 raw37283step1Labels := by
      have ha : raw37283step1 = raw37283step0 := by apply Matrix.ext; unfold raw37283step1 raw37283step0; decide +kernel
      have hl : raw37283step0Labels = labelEmbedding6 ∘ raw37283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37283step0 raw37283step0Labels raw37283step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw37284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw37284step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw37284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37284 raw37284Labels = mixedMoment B node4762 node4762Labels := by
  calc
    mixedMoment B raw37284 raw37284Labels = mixedMoment B raw37284step0 raw37284step0Labels := by
      have ha : raw37284step0 = (fun i j => raw37284 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37284step0 raw37284; decide +kernel
      have hl : raw37284step0Labels = raw37284Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37284 raw37284Labels permutation153 permutation3
    mixedMoment B raw37284step0 raw37284step0Labels = mixedMoment B raw37284step1 raw37284step1Labels := by
      have ha : raw37284step1 = raw37284step0 := by apply Matrix.ext; unfold raw37284step1 raw37284step0; decide +kernel
      have hl : raw37284step0Labels = labelEmbedding6 ∘ raw37284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37284step0 raw37284step0Labels raw37284step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4762 node4762Labels := by rfl

def raw37285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37285step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37285 raw37285Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw37285 raw37285Labels = mixedMoment B raw37285step0 raw37285step0Labels := by
      have ha : raw37285step0 = (fun i j => raw37285 (permutation589 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37285step0 raw37285; decide +kernel
      have hl : raw37285step0Labels = raw37285Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37285 raw37285Labels permutation589 permutation5
    mixedMoment B raw37285step0 raw37285step0Labels = mixedMoment B raw37285step1 raw37285step1Labels := by
      have ha : raw37285step1 = raw37285step0 := by apply Matrix.ext; unfold raw37285step1 raw37285step0; decide +kernel
      have hl : raw37285step0Labels = labelEmbedding8 ∘ raw37285step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37285step0 raw37285step0Labels raw37285step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

def raw37286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37286step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37286 raw37286Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw37286 raw37286Labels = mixedMoment B raw37286step0 raw37286step0Labels := by
      have ha : raw37286step0 = (fun i j => raw37286 (permutation587 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37286step0 raw37286; decide +kernel
      have hl : raw37286step0Labels = raw37286Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37286 raw37286Labels permutation587 permutation5
    mixedMoment B raw37286step0 raw37286step0Labels = mixedMoment B raw37286step1 raw37286step1Labels := by
      have ha : raw37286step1 = raw37286step0 := by apply Matrix.ext; unfold raw37286step1 raw37286step0; decide +kernel
      have hl : raw37286step0Labels = labelEmbedding8 ∘ raw37286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37286step0 raw37286step0Labels raw37286step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

def raw37287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37287step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37287 raw37287Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw37287 raw37287Labels = mixedMoment B raw37287step0 raw37287step0Labels := by
      have ha : raw37287step0 = (fun i j => raw37287 (permutation577 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37287step0 raw37287; decide +kernel
      have hl : raw37287step0Labels = raw37287Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37287 raw37287Labels permutation577 permutation5
    mixedMoment B raw37287step0 raw37287step0Labels = mixedMoment B raw37287step1 raw37287step1Labels := by
      have ha : raw37287step1 = raw37287step0 := by apply Matrix.ext; unfold raw37287step1 raw37287step0; decide +kernel
      have hl : raw37287step0Labels = labelEmbedding8 ∘ raw37287step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37287step0 raw37287step0Labels raw37287step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw37288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw37288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37288step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37288 raw37288Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw37288 raw37288Labels = mixedMoment B raw37288step0 raw37288step0Labels := by
      have ha : raw37288step0 = (fun i j => raw37288 (permutation557 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37288step0 raw37288; decide +kernel
      have hl : raw37288step0Labels = raw37288Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37288 raw37288Labels permutation557 permutation5
    mixedMoment B raw37288step0 raw37288step0Labels = mixedMoment B raw37288step1 raw37288step1Labels := by
      have ha : raw37288step1 = raw37288step0 := by apply Matrix.ext; unfold raw37288step1 raw37288step0; decide +kernel
      have hl : raw37288step0Labels = labelEmbedding8 ∘ raw37288step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37288step0 raw37288step0Labels raw37288step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw37289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw37289step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw37289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37289 raw37289Labels = mixedMoment B node4761 node4761Labels := by
  calc
    mixedMoment B raw37289 raw37289Labels = mixedMoment B raw37289step0 raw37289step0Labels := by
      have ha : raw37289step0 = (fun i j => raw37289 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37289step0 raw37289; decide +kernel
      have hl : raw37289step0Labels = raw37289Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37289 raw37289Labels permutation152 permutation3
    mixedMoment B raw37289step0 raw37289step0Labels = mixedMoment B raw37289step1 raw37289step1Labels := by
      have ha : raw37289step1 = raw37289step0 := by apply Matrix.ext; unfold raw37289step1 raw37289step0; decide +kernel
      have hl : raw37289step0Labels = labelEmbedding6 ∘ raw37289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37289step0 raw37289step0Labels raw37289step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4761 node4761Labels := by rfl

def raw37290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw37290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37290 raw37290Labels = mixedMoment B node5044 node5044Labels := by
  calc
    mixedMoment B raw37290 raw37290Labels = mixedMoment B raw37290step0 raw37290step0Labels := by
      have ha : raw37290step0 = (fun i j => raw37290 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37290step0 raw37290; decide +kernel
      have hl : raw37290step0Labels = raw37290Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37290 raw37290Labels permutation663 permutation2
    mixedMoment B raw37290step0 raw37290step0Labels = mixedMoment B raw37290step1 raw37290step1Labels := by
      have ha : raw37290step1 = -raw37290step0 := by apply Matrix.ext; change ∀ i j, raw37290step1 i j = -(raw37290step0 i j); unfold raw37290step1 raw37290step0; decide +kernel
      have hl : raw37290step1Labels = raw37290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5044 node5044Labels := by rfl

def raw37291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw37291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37291 raw37291Labels = mixedMoment B node5044 node5044Labels := by
  calc
    mixedMoment B raw37291 raw37291Labels = mixedMoment B raw37291step0 raw37291step0Labels := by
      have ha : raw37291step0 = (fun i j => raw37291 (permutation661 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37291step0 raw37291; decide +kernel
      have hl : raw37291step0Labels = raw37291Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37291 raw37291Labels permutation661 permutation2
    mixedMoment B raw37291step0 raw37291step0Labels = mixedMoment B raw37291step1 raw37291step1Labels := by
      have ha : raw37291step1 = -raw37291step0 := by apply Matrix.ext; change ∀ i j, raw37291step1 i j = -(raw37291step0 i j); unfold raw37291step1 raw37291step0; decide +kernel
      have hl : raw37291step1Labels = raw37291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5044 node5044Labels := by rfl

def raw37292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37292 raw37292Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw37292 raw37292Labels = mixedMoment B raw37292step0 raw37292step0Labels := by
      have ha : raw37292step0 = (fun i j => raw37292 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37292step0 raw37292; decide +kernel
      have hl : raw37292step0Labels = raw37292Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37292 raw37292Labels permutation686 permutation2
    mixedMoment B raw37292step0 raw37292step0Labels = mixedMoment B raw37292step1 raw37292step1Labels := by
      have ha : raw37292step1 = -raw37292step0 := by apply Matrix.ext; change ∀ i j, raw37292step1 i j = -(raw37292step0 i j); unfold raw37292step1 raw37292step0; decide +kernel
      have hl : raw37292step1Labels = raw37292step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw37293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw37293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37293 raw37293Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw37293 raw37293Labels = mixedMoment B raw37293step0 raw37293step0Labels := by
      have ha : raw37293step0 = (fun i j => raw37293 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37293step0 raw37293; decide +kernel
      have hl : raw37293step0Labels = raw37293Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37293 raw37293Labels permutation662 permutation2
    mixedMoment B raw37293step0 raw37293step0Labels = mixedMoment B raw37293step1 raw37293step1Labels := by
      have ha : raw37293step1 = -raw37293step0 := by apply Matrix.ext; change ∀ i j, raw37293step1 i j = -(raw37293step0 i j); unfold raw37293step1 raw37293step0; decide +kernel
      have hl : raw37293step1Labels = raw37293step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw37294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37294 raw37294Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw37294 raw37294Labels = mixedMoment B raw37294step0 raw37294step0Labels := by
      have ha : raw37294step0 = (fun i j => raw37294 (permutation651 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37294step0 raw37294; decide +kernel
      have hl : raw37294step0Labels = raw37294Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37294 raw37294Labels permutation651 permutation7
    mixedMoment B raw37294step0 raw37294step0Labels = mixedMoment B raw37294step1 raw37294step1Labels := by
      have ha : raw37294step1 = raw37294step0 := by apply Matrix.ext; unfold raw37294step1 raw37294step0; decide +kernel
      have hl : raw37294step0Labels = labelEmbedding1 ∘ raw37294step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37294step0 raw37294step0Labels raw37294step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw37295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37295 raw37295Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw37295 raw37295Labels = mixedMoment B raw37295step0 raw37295step0Labels := by
      have ha : raw37295step0 = (fun i j => raw37295 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37295step0 raw37295; decide +kernel
      have hl : raw37295step0Labels = raw37295Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37295 raw37295Labels permutation650 permutation7
    mixedMoment B raw37295step0 raw37295step0Labels = mixedMoment B raw37295step1 raw37295step1Labels := by
      have ha : raw37295step1 = raw37295step0 := by apply Matrix.ext; unfold raw37295step1 raw37295step0; decide +kernel
      have hl : raw37295step0Labels = labelEmbedding1 ∘ raw37295step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37295step0 raw37295step0Labels raw37295step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw37296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37296 raw37296Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw37296 raw37296Labels = mixedMoment B raw37296step0 raw37296step0Labels := by
      have ha : raw37296step0 = (fun i j => raw37296 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37296step0 raw37296; decide +kernel
      have hl : raw37296step0Labels = raw37296Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37296 raw37296Labels permutation650 permutation7
    mixedMoment B raw37296step0 raw37296step0Labels = mixedMoment B raw37296step1 raw37296step1Labels := by
      have ha : raw37296step1 = raw37296step0 := by apply Matrix.ext; unfold raw37296step1 raw37296step0; decide +kernel
      have hl : raw37296step0Labels = labelEmbedding1 ∘ raw37296step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37296step0 raw37296step0Labels raw37296step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw37297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37297step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37297 raw37297Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw37297 raw37297Labels = mixedMoment B raw37297step0 raw37297step0Labels := by
      have ha : raw37297step0 = (fun i j => raw37297 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37297step0 raw37297; decide +kernel
      have hl : raw37297step0Labels = raw37297Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37297 raw37297Labels permutation650 permutation7
    mixedMoment B raw37297step0 raw37297step0Labels = mixedMoment B raw37297step1 raw37297step1Labels := by
      have ha : raw37297step1 = raw37297step0 := by apply Matrix.ext; unfold raw37297step1 raw37297step0; decide +kernel
      have hl : raw37297step0Labels = labelEmbedding1 ∘ raw37297step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37297step0 raw37297step0Labels raw37297step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

def raw37298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37298step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37298 raw37298Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw37298 raw37298Labels = mixedMoment B raw37298step0 raw37298step0Labels := by
      have ha : raw37298step0 = (fun i j => raw37298 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37298step0 raw37298; decide +kernel
      have hl : raw37298step0Labels = raw37298Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37298 raw37298Labels permutation650 permutation7
    mixedMoment B raw37298step0 raw37298step0Labels = mixedMoment B raw37298step1 raw37298step1Labels := by
      have ha : raw37298step1 = raw37298step0 := by apply Matrix.ext; unfold raw37298step1 raw37298step0; decide +kernel
      have hl : raw37298step0Labels = labelEmbedding1 ∘ raw37298step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37298step0 raw37298step0Labels raw37298step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw37299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37299step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37299step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37299step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37299 raw37299Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw37299 raw37299Labels = mixedMoment B raw37299step0 raw37299step0Labels := by
      have ha : raw37299step0 = (fun i j => raw37299 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37299step0 raw37299; decide +kernel
      have hl : raw37299step0Labels = raw37299Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37299 raw37299Labels permutation186 permutation5
    mixedMoment B raw37299step0 raw37299step0Labels = mixedMoment B raw37299step1 raw37299step1Labels := by
      have ha : raw37299step1 = -raw37299step0 := by apply Matrix.ext; change ∀ i j, raw37299step1 i j = -(raw37299step0 i j); unfold raw37299step1 raw37299step0; decide +kernel
      have hl : raw37299step1Labels = raw37299step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37299step1 raw37299step1Labels = mixedMoment B raw37299step2 raw37299step2Labels := by
      have ha : raw37299step2 = raw37299step1 := by apply Matrix.ext; unfold raw37299step2 raw37299step1; decide +kernel
      have hl : raw37299step1Labels = labelEmbedding1 ∘ raw37299step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37299step1 raw37299step1Labels raw37299step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw37300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37300step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37300 raw37300Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw37300 raw37300Labels = mixedMoment B raw37300step0 raw37300step0Labels := by
      have ha : raw37300step0 = (fun i j => raw37300 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37300step0 raw37300; decide +kernel
      have hl : raw37300step0Labels = raw37300Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37300 raw37300Labels permutation186 permutation5
    mixedMoment B raw37300step0 raw37300step0Labels = mixedMoment B raw37300step1 raw37300step1Labels := by
      have ha : raw37300step1 = -raw37300step0 := by apply Matrix.ext; change ∀ i j, raw37300step1 i j = -(raw37300step0 i j); unfold raw37300step1 raw37300step0; decide +kernel
      have hl : raw37300step1Labels = raw37300step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37300step1 raw37300step1Labels = mixedMoment B raw37300step2 raw37300step2Labels := by
      have ha : raw37300step2 = raw37300step1 := by apply Matrix.ext; unfold raw37300step2 raw37300step1; decide +kernel
      have hl : raw37300step1Labels = labelEmbedding1 ∘ raw37300step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37300step1 raw37300step1Labels raw37300step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw37301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37301step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37301step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37301step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37301 raw37301Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw37301 raw37301Labels = mixedMoment B raw37301step0 raw37301step0Labels := by
      have ha : raw37301step0 = (fun i j => raw37301 (permutation210 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37301step0 raw37301; decide +kernel
      have hl : raw37301step0Labels = raw37301Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37301 raw37301Labels permutation210 permutation5
    mixedMoment B raw37301step0 raw37301step0Labels = mixedMoment B raw37301step1 raw37301step1Labels := by
      have ha : raw37301step1 = -raw37301step0 := by apply Matrix.ext; change ∀ i j, raw37301step1 i j = -(raw37301step0 i j); unfold raw37301step1 raw37301step0; decide +kernel
      have hl : raw37301step1Labels = raw37301step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37301step1 raw37301step1Labels = mixedMoment B raw37301step2 raw37301step2Labels := by
      have ha : raw37301step2 = raw37301step1 := by apply Matrix.ext; unfold raw37301step2 raw37301step1; decide +kernel
      have hl : raw37301step1Labels = labelEmbedding1 ∘ raw37301step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37301step1 raw37301step1Labels raw37301step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw37302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37302step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37302step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37302 raw37302Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw37302 raw37302Labels = mixedMoment B raw37302step0 raw37302step0Labels := by
      have ha : raw37302step0 = (fun i j => raw37302 (permutation648 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37302step0 raw37302; decide +kernel
      have hl : raw37302step0Labels = raw37302Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37302 raw37302Labels permutation648 permutation7
    mixedMoment B raw37302step0 raw37302step0Labels = mixedMoment B raw37302step1 raw37302step1Labels := by
      have ha : raw37302step1 = raw37302step0 := by apply Matrix.ext; unfold raw37302step1 raw37302step0; decide +kernel
      have hl : raw37302step0Labels = labelEmbedding1 ∘ raw37302step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37302step0 raw37302step0Labels raw37302step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw37303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw37303step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37303step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37303step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37303 raw37303Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw37303 raw37303Labels = mixedMoment B raw37303step0 raw37303step0Labels := by
      have ha : raw37303step0 = (fun i j => raw37303 (permutation254 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37303step0 raw37303; decide +kernel
      have hl : raw37303step0Labels = raw37303Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37303 raw37303Labels permutation254 permutation5
    mixedMoment B raw37303step0 raw37303step0Labels = mixedMoment B raw37303step1 raw37303step1Labels := by
      have ha : raw37303step1 = -raw37303step0 := by apply Matrix.ext; change ∀ i j, raw37303step1 i j = -(raw37303step0 i j); unfold raw37303step1 raw37303step0; decide +kernel
      have hl : raw37303step1Labels = raw37303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37303step1 raw37303step1Labels = mixedMoment B raw37303step2 raw37303step2Labels := by
      have ha : raw37303step2 = raw37303step1 := by apply Matrix.ext; unfold raw37303step2 raw37303step1; decide +kernel
      have hl : raw37303step1Labels = labelEmbedding1 ∘ raw37303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37303step1 raw37303step1Labels raw37303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw37304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37304step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37304 raw37304Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw37304 raw37304Labels = mixedMoment B raw37304step0 raw37304step0Labels := by
      have ha : raw37304step0 = (fun i j => raw37304 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37304step0 raw37304; decide +kernel
      have hl : raw37304step0Labels = raw37304Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37304 raw37304Labels permutation162 permutation5
    mixedMoment B raw37304step0 raw37304step0Labels = mixedMoment B raw37304step1 raw37304step1Labels := by
      have ha : raw37304step1 = -raw37304step0 := by apply Matrix.ext; change ∀ i j, raw37304step1 i j = -(raw37304step0 i j); unfold raw37304step1 raw37304step0; decide +kernel
      have hl : raw37304step1Labels = raw37304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37304step1 raw37304step1Labels = mixedMoment B raw37304step2 raw37304step2Labels := by
      have ha : raw37304step2 = raw37304step1 := by apply Matrix.ext; unfold raw37304step2 raw37304step1; decide +kernel
      have hl : raw37304step1Labels = labelEmbedding1 ∘ raw37304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37304step1 raw37304step1Labels raw37304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw37305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37305step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37305step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37305 raw37305Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw37305 raw37305Labels = mixedMoment B raw37305step0 raw37305step0Labels := by
      have ha : raw37305step0 = (fun i j => raw37305 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37305step0 raw37305; decide +kernel
      have hl : raw37305step0Labels = raw37305Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37305 raw37305Labels permutation162 permutation5
    mixedMoment B raw37305step0 raw37305step0Labels = mixedMoment B raw37305step1 raw37305step1Labels := by
      have ha : raw37305step1 = -raw37305step0 := by apply Matrix.ext; change ∀ i j, raw37305step1 i j = -(raw37305step0 i j); unfold raw37305step1 raw37305step0; decide +kernel
      have hl : raw37305step1Labels = raw37305step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37305step1 raw37305step1Labels = mixedMoment B raw37305step2 raw37305step2Labels := by
      have ha : raw37305step2 = raw37305step1 := by apply Matrix.ext; unfold raw37305step2 raw37305step1; decide +kernel
      have hl : raw37305step1Labels = labelEmbedding1 ∘ raw37305step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37305step1 raw37305step1Labels raw37305step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw37306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37306step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37306step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37306step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37306 raw37306Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw37306 raw37306Labels = mixedMoment B raw37306step0 raw37306step0Labels := by
      have ha : raw37306step0 = (fun i j => raw37306 (permutation204 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37306step0 raw37306; decide +kernel
      have hl : raw37306step0Labels = raw37306Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37306 raw37306Labels permutation204 permutation5
    mixedMoment B raw37306step0 raw37306step0Labels = mixedMoment B raw37306step1 raw37306step1Labels := by
      have ha : raw37306step1 = -raw37306step0 := by apply Matrix.ext; change ∀ i j, raw37306step1 i j = -(raw37306step0 i j); unfold raw37306step1 raw37306step0; decide +kernel
      have hl : raw37306step1Labels = raw37306step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37306step1 raw37306step1Labels = mixedMoment B raw37306step2 raw37306step2Labels := by
      have ha : raw37306step2 = raw37306step1 := by apply Matrix.ext; unfold raw37306step2 raw37306step1; decide +kernel
      have hl : raw37306step1Labels = labelEmbedding1 ∘ raw37306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37306step1 raw37306step1Labels raw37306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw37307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37307step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37307step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37307 raw37307Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw37307 raw37307Labels = mixedMoment B raw37307step0 raw37307step0Labels := by
      have ha : raw37307step0 = (fun i j => raw37307 (permutation649 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37307step0 raw37307; decide +kernel
      have hl : raw37307step0Labels = raw37307Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37307 raw37307Labels permutation649 permutation7
    mixedMoment B raw37307step0 raw37307step0Labels = mixedMoment B raw37307step1 raw37307step1Labels := by
      have ha : raw37307step1 = raw37307step0 := by apply Matrix.ext; unfold raw37307step1 raw37307step0; decide +kernel
      have hl : raw37307step0Labels = labelEmbedding1 ∘ raw37307step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37307step0 raw37307step0Labels raw37307step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw37308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw37308step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37308step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37308step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37308 raw37308Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw37308 raw37308Labels = mixedMoment B raw37308step0 raw37308step0Labels := by
      have ha : raw37308step0 = (fun i j => raw37308 (permutation248 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37308step0 raw37308; decide +kernel
      have hl : raw37308step0Labels = raw37308Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37308 raw37308Labels permutation248 permutation5
    mixedMoment B raw37308step0 raw37308step0Labels = mixedMoment B raw37308step1 raw37308step1Labels := by
      have ha : raw37308step1 = -raw37308step0 := by apply Matrix.ext; change ∀ i j, raw37308step1 i j = -(raw37308step0 i j); unfold raw37308step1 raw37308step0; decide +kernel
      have hl : raw37308step1Labels = raw37308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37308step1 raw37308step1Labels = mixedMoment B raw37308step2 raw37308step2Labels := by
      have ha : raw37308step2 = raw37308step1 := by apply Matrix.ext; unfold raw37308step2 raw37308step1; decide +kernel
      have hl : raw37308step1Labels = labelEmbedding1 ∘ raw37308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37308step1 raw37308step1Labels raw37308step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw37309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37309step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37309step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37309step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37309step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37309 raw37309Labels = mixedMoment B node2178 node2178Labels := by
  calc
    mixedMoment B raw37309 raw37309Labels = mixedMoment B raw37309step0 raw37309step0Labels := by
      have ha : raw37309step0 = (fun i j => raw37309 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37309step0 raw37309; decide +kernel
      have hl : raw37309step0Labels = raw37309Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37309 raw37309Labels permutation156 permutation5
    mixedMoment B raw37309step0 raw37309step0Labels = mixedMoment B raw37309step1 raw37309step1Labels := by
      have ha : raw37309step1 = -raw37309step0 := by apply Matrix.ext; change ∀ i j, raw37309step1 i j = -(raw37309step0 i j); unfold raw37309step1 raw37309step0; decide +kernel
      have hl : raw37309step1Labels = raw37309step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37309step1 raw37309step1Labels = mixedMoment B raw37309step2 raw37309step2Labels := by
      have ha : raw37309step2 = raw37309step1 := by apply Matrix.ext; unfold raw37309step2 raw37309step1; decide +kernel
      have hl : raw37309step1Labels = labelEmbedding1 ∘ raw37309step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37309step1 raw37309step1Labels raw37309step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2178 node2178Labels := by rfl

def raw37310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37310step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37310step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37310 raw37310Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw37310 raw37310Labels = mixedMoment B raw37310step0 raw37310step0Labels := by
      have ha : raw37310step0 = (fun i j => raw37310 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37310step0 raw37310; decide +kernel
      have hl : raw37310step0Labels = raw37310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37310 raw37310Labels permutation156 permutation5
    mixedMoment B raw37310step0 raw37310step0Labels = mixedMoment B raw37310step1 raw37310step1Labels := by
      have ha : raw37310step1 = -raw37310step0 := by apply Matrix.ext; change ∀ i j, raw37310step1 i j = -(raw37310step0 i j); unfold raw37310step1 raw37310step0; decide +kernel
      have hl : raw37310step1Labels = raw37310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37310step1 raw37310step1Labels = mixedMoment B raw37310step2 raw37310step2Labels := by
      have ha : raw37310step2 = raw37310step1 := by apply Matrix.ext; unfold raw37310step2 raw37310step1; decide +kernel
      have hl : raw37310step1Labels = labelEmbedding1 ∘ raw37310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37310step1 raw37310step1Labels raw37310step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

def raw37311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37311step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37311step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37311step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37311 raw37311Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw37311 raw37311Labels = mixedMoment B raw37311step0 raw37311step0Labels := by
      have ha : raw37311step0 = (fun i j => raw37311 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37311step0 raw37311; decide +kernel
      have hl : raw37311step0Labels = raw37311Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37311 raw37311Labels permutation180 permutation5
    mixedMoment B raw37311step0 raw37311step0Labels = mixedMoment B raw37311step1 raw37311step1Labels := by
      have ha : raw37311step1 = -raw37311step0 := by apply Matrix.ext; change ∀ i j, raw37311step1 i j = -(raw37311step0 i j); unfold raw37311step1 raw37311step0; decide +kernel
      have hl : raw37311step1Labels = raw37311step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37311step1 raw37311step1Labels = mixedMoment B raw37311step2 raw37311step2Labels := by
      have ha : raw37311step2 = raw37311step1 := by apply Matrix.ext; unfold raw37311step2 raw37311step1; decide +kernel
      have hl : raw37311step1Labels = labelEmbedding1 ∘ raw37311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37311step1 raw37311step1Labels raw37311step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

def raw37312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37312 raw37312Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw37312 raw37312Labels = mixedMoment B raw37312step0 raw37312step0Labels := by
      have ha : raw37312step0 = (fun i j => raw37312 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37312step0 raw37312; decide +kernel
      have hl : raw37312step0Labels = raw37312Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37312 raw37312Labels permutation650 permutation7
    mixedMoment B raw37312step0 raw37312step0Labels = mixedMoment B raw37312step1 raw37312step1Labels := by
      have ha : raw37312step1 = raw37312step0 := by apply Matrix.ext; unfold raw37312step1 raw37312step0; decide +kernel
      have hl : raw37312step0Labels = labelEmbedding1 ∘ raw37312step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37312step0 raw37312step0Labels raw37312step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

def raw37313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37313step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37313step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw37313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37313step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw37313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37313 raw37313Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw37313 raw37313Labels = mixedMoment B raw37313step0 raw37313step0Labels := by
      have ha : raw37313step0 = (fun i j => raw37313 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37313step0 raw37313; decide +kernel
      have hl : raw37313step0Labels = raw37313Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37313 raw37313Labels permutation246 permutation5
    mixedMoment B raw37313step0 raw37313step0Labels = mixedMoment B raw37313step1 raw37313step1Labels := by
      have ha : raw37313step1 = -raw37313step0 := by apply Matrix.ext; change ∀ i j, raw37313step1 i j = -(raw37313step0 i j); unfold raw37313step1 raw37313step0; decide +kernel
      have hl : raw37313step1Labels = raw37313step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37313step1 raw37313step1Labels = mixedMoment B raw37313step2 raw37313step2Labels := by
      have ha : raw37313step2 = raw37313step1 := by apply Matrix.ext; unfold raw37313step2 raw37313step1; decide +kernel
      have hl : raw37313step1Labels = labelEmbedding1 ∘ raw37313step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37313step1 raw37313step1Labels raw37313step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

def raw37314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw37314step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw37314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37314step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw37314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37314 raw37314Labels = mixedMoment B node2171 node2171Labels := by
  calc
    mixedMoment B raw37314 raw37314Labels = mixedMoment B raw37314step0 raw37314step0Labels := by
      have ha : raw37314step0 = (fun i j => raw37314 (permutation153 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37314step0 raw37314; decide +kernel
      have hl : raw37314step0Labels = raw37314Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37314 raw37314Labels permutation153 permutation5
    mixedMoment B raw37314step0 raw37314step0Labels = mixedMoment B raw37314step1 raw37314step1Labels := by
      have ha : raw37314step1 = -raw37314step0 := by apply Matrix.ext; change ∀ i j, raw37314step1 i j = -(raw37314step0 i j); unfold raw37314step1 raw37314step0; decide +kernel
      have hl : raw37314step1Labels = raw37314step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37314step1 raw37314step1Labels = mixedMoment B raw37314step2 raw37314step2Labels := by
      have ha : raw37314step2 = raw37314step1 := by apply Matrix.ext; unfold raw37314step2 raw37314step1; decide +kernel
      have hl : raw37314step1Labels = labelEmbedding1 ∘ raw37314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37314step1 raw37314step1Labels raw37314step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2171 node2171Labels := by rfl

def raw37315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37315step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37315 raw37315Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw37315 raw37315Labels = mixedMoment B raw37315step0 raw37315step0Labels := by
      have ha : raw37315step0 = (fun i j => raw37315 (permutation589 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37315step0 raw37315; decide +kernel
      have hl : raw37315step0Labels = raw37315Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37315 raw37315Labels permutation589 permutation5
    mixedMoment B raw37315step0 raw37315step0Labels = mixedMoment B raw37315step1 raw37315step1Labels := by
      have ha : raw37315step1 = raw37315step0 := by apply Matrix.ext; unfold raw37315step1 raw37315step0; decide +kernel
      have hl : raw37315step0Labels = labelEmbedding1 ∘ raw37315step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37315step0 raw37315step0Labels raw37315step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

def raw37316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37316 raw37316Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw37316 raw37316Labels = mixedMoment B raw37316step0 raw37316step0Labels := by
      have ha : raw37316step0 = (fun i j => raw37316 (permutation587 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37316step0 raw37316; decide +kernel
      have hl : raw37316step0Labels = raw37316Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37316 raw37316Labels permutation587 permutation5
    mixedMoment B raw37316step0 raw37316step0Labels = mixedMoment B raw37316step1 raw37316step1Labels := by
      have ha : raw37316step1 = raw37316step0 := by apply Matrix.ext; unfold raw37316step1 raw37316step0; decide +kernel
      have hl : raw37316step0Labels = labelEmbedding1 ∘ raw37316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37316step0 raw37316step0Labels raw37316step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

def raw37317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37317step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37317 raw37317Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw37317 raw37317Labels = mixedMoment B raw37317step0 raw37317step0Labels := by
      have ha : raw37317step0 = (fun i j => raw37317 (permutation577 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37317step0 raw37317; decide +kernel
      have hl : raw37317step0Labels = raw37317Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37317 raw37317Labels permutation577 permutation5
    mixedMoment B raw37317step0 raw37317step0Labels = mixedMoment B raw37317step1 raw37317step1Labels := by
      have ha : raw37317step1 = raw37317step0 := by apply Matrix.ext; unfold raw37317step1 raw37317step0; decide +kernel
      have hl : raw37317step0Labels = labelEmbedding1 ∘ raw37317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37317step0 raw37317step0Labels raw37317step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw37318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw37318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37318 raw37318Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw37318 raw37318Labels = mixedMoment B raw37318step0 raw37318step0Labels := by
      have ha : raw37318step0 = (fun i j => raw37318 (permutation557 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37318step0 raw37318; decide +kernel
      have hl : raw37318step0Labels = raw37318Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37318 raw37318Labels permutation557 permutation5
    mixedMoment B raw37318step0 raw37318step0Labels = mixedMoment B raw37318step1 raw37318step1Labels := by
      have ha : raw37318step1 = raw37318step0 := by apply Matrix.ext; unfold raw37318step1 raw37318step0; decide +kernel
      have hl : raw37318step0Labels = labelEmbedding1 ∘ raw37318step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37318step0 raw37318step0Labels raw37318step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw37319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37319step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37319step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37319 raw37319Labels = mixedMoment B node2175 node2175Labels := by
  calc
    mixedMoment B raw37319 raw37319Labels = mixedMoment B raw37319step0 raw37319step0Labels := by
      have ha : raw37319step0 = (fun i j => raw37319 (permutation153 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37319step0 raw37319; decide +kernel
      have hl : raw37319step0Labels = raw37319Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37319 raw37319Labels permutation153 permutation5
    mixedMoment B raw37319step0 raw37319step0Labels = mixedMoment B raw37319step1 raw37319step1Labels := by
      have ha : raw37319step1 = -raw37319step0 := by apply Matrix.ext; change ∀ i j, raw37319step1 i j = -(raw37319step0 i j); unfold raw37319step1 raw37319step0; decide +kernel
      have hl : raw37319step1Labels = raw37319step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37319step1 raw37319step1Labels = mixedMoment B raw37319step2 raw37319step2Labels := by
      have ha : raw37319step2 = raw37319step1 := by apply Matrix.ext; unfold raw37319step2 raw37319step1; decide +kernel
      have hl : raw37319step1Labels = labelEmbedding1 ∘ raw37319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37319step1 raw37319step1Labels raw37319step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2175 node2175Labels := by rfl

def raw37320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37320 raw37320Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw37320 raw37320Labels = mixedMoment B raw37320step0 raw37320step0Labels := by
      have ha : raw37320step0 = (fun i j => raw37320 (permutation651 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37320step0 raw37320; decide +kernel
      have hl : raw37320step0Labels = raw37320Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37320 raw37320Labels permutation651 permutation7
    mixedMoment B raw37320step0 raw37320step0Labels = mixedMoment B raw37320step1 raw37320step1Labels := by
      have ha : raw37320step1 = raw37320step0 := by apply Matrix.ext; unfold raw37320step1 raw37320step0; decide +kernel
      have hl : raw37320step0Labels = labelEmbedding1 ∘ raw37320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37320step0 raw37320step0Labels raw37320step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

def raw37321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37321 raw37321Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw37321 raw37321Labels = mixedMoment B raw37321step0 raw37321step0Labels := by
      have ha : raw37321step0 = (fun i j => raw37321 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37321step0 raw37321; decide +kernel
      have hl : raw37321step0Labels = raw37321Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37321 raw37321Labels permutation650 permutation7
    mixedMoment B raw37321step0 raw37321step0Labels = mixedMoment B raw37321step1 raw37321step1Labels := by
      have ha : raw37321step1 = raw37321step0 := by apply Matrix.ext; unfold raw37321step1 raw37321step0; decide +kernel
      have hl : raw37321step0Labels = labelEmbedding1 ∘ raw37321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37321step0 raw37321step0Labels raw37321step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

def raw37322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37322 raw37322Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw37322 raw37322Labels = mixedMoment B raw37322step0 raw37322step0Labels := by
      have ha : raw37322step0 = (fun i j => raw37322 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37322step0 raw37322; decide +kernel
      have hl : raw37322step0Labels = raw37322Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37322 raw37322Labels permutation650 permutation7
    mixedMoment B raw37322step0 raw37322step0Labels = mixedMoment B raw37322step1 raw37322step1Labels := by
      have ha : raw37322step1 = raw37322step0 := by apply Matrix.ext; unfold raw37322step1 raw37322step0; decide +kernel
      have hl : raw37322step0Labels = labelEmbedding1 ∘ raw37322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37322step0 raw37322step0Labels raw37322step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw37323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw37323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37323step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37323 raw37323Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw37323 raw37323Labels = mixedMoment B raw37323step0 raw37323step0Labels := by
      have ha : raw37323step0 = (fun i j => raw37323 (permutation650 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37323step0 raw37323; decide +kernel
      have hl : raw37323step0Labels = raw37323Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37323 raw37323Labels permutation650 permutation7
    mixedMoment B raw37323step0 raw37323step0Labels = mixedMoment B raw37323step1 raw37323step1Labels := by
      have ha : raw37323step1 = raw37323step0 := by apply Matrix.ext; unfold raw37323step1 raw37323step0; decide +kernel
      have hl : raw37323step0Labels = labelEmbedding1 ∘ raw37323step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37323step0 raw37323step0Labels raw37323step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

def raw37324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37324step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37324step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37324step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37324 raw37324Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37324 raw37324Labels = mixedMoment B raw37324step0 raw37324step0Labels := by
      have hz : ∀ j, raw37324 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37324step0 = (fun i j => raw37324 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37324step0 raw37324; decide +kernel
      have hl : raw37324step0Labels = raw37324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37324 raw37324Labels permutation265 hz
    mixedMoment B raw37324step0 raw37324step0Labels = mixedMoment B raw37324step1 raw37324step1Labels := by
      have hz : ∀ i, raw37324step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37324step1 = (fun i j => raw37324step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37324step1 raw37324step0; decide +kernel
      have hl : raw37324step1Labels = (fun j => raw37324step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37324step0 raw37324step0Labels permutation6 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw37325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37325step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![2, -2]]
def raw37325step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37325step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37325step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37325 raw37325Labels = mixedMoment B node4086 node4086Labels := by
  calc
    mixedMoment B raw37325 raw37325Labels = mixedMoment B raw37325step0 raw37325step0Labels := by
      have hz : ∀ i, raw37325 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37325step0 = (fun i j => raw37325 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37325step0 raw37325; decide +kernel
      have hl : raw37325step0Labels = (fun j => raw37325Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37325 raw37325Labels permutation6 hz
    mixedMoment B raw37325step0 raw37325step0Labels = mixedMoment B raw37325step1 raw37325step1Labels := by
      have ha : raw37325step1 = (fun i j => raw37325step0 (permutation178 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37325step1 raw37325step0; decide +kernel
      have hl : raw37325step1Labels = raw37325step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37325step0 raw37325step0Labels permutation178 permutation0
    _ = mixedMoment B node4086 node4086Labels := by rfl

def raw37326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw37326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw37326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37326step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw37326step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37326step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw37326step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37326step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37326step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37326 raw37326Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37326 raw37326Labels = mixedMoment B raw37326step0 raw37326step0Labels := by
      have hz : ∀ j, raw37326 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37326step0 = (fun i j => raw37326 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37326step0 raw37326; decide +kernel
      have hl : raw37326step0Labels = raw37326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37326 raw37326Labels permutation520 hz
    mixedMoment B raw37326step0 raw37326step0Labels = mixedMoment B raw37326step1 raw37326step1Labels := by
      have hz : ∀ i, raw37326step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37326step1 = (fun i j => raw37326step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37326step1 raw37326step0; decide +kernel
      have hl : raw37326step1Labels = (fun j => raw37326step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37326step0 raw37326step0Labels permutation6 hz
    mixedMoment B raw37326step1 raw37326step1Labels = mixedMoment B raw37326step2 raw37326step2Labels := by
      have ha : raw37326step2 = (fun i j => raw37326step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37326step2 raw37326step1; decide +kernel
      have hl : raw37326step2Labels = raw37326step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37326step1 raw37326step1Labels permutation125 permutation0
    mixedMoment B raw37326step2 raw37326step2Labels = mixedMoment B raw37326step3 raw37326step3Labels := by
      have ha : raw37326step3 = -raw37326step2 := by apply Matrix.ext; change ∀ i j, raw37326step3 i j = -(raw37326step2 i j); unfold raw37326step3 raw37326step2; decide +kernel
      have hl : raw37326step3Labels = raw37326step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw37327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw37327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37327step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw37327step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37327step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37327step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37327 raw37327Labels = mixedMoment B node4086 node4086Labels := by
  calc
    mixedMoment B raw37327 raw37327Labels = mixedMoment B raw37327step0 raw37327step0Labels := by
      have hz : ∀ i, raw37327 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37327step0 = (fun i j => raw37327 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37327step0 raw37327; decide +kernel
      have hl : raw37327step0Labels = (fun j => raw37327Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37327 raw37327Labels permutation6 hz
    mixedMoment B raw37327step0 raw37327step0Labels = mixedMoment B raw37327step1 raw37327step1Labels := by
      have ha : raw37327step1 = (fun i j => raw37327step0 (permutation176 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37327step1 raw37327step0; decide +kernel
      have hl : raw37327step1Labels = raw37327step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37327step0 raw37327step0Labels permutation176 permutation0
    _ = mixedMoment B node4086 node4086Labels := by rfl

def raw37328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37328step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw37328step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37328step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![1, -1], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37328step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37328step2 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37328step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37328 raw37328Labels = mixedMoment B node4078 node4078Labels := by
  calc
    mixedMoment B raw37328 raw37328Labels = mixedMoment B raw37328step0 raw37328step0Labels := by
      have hz : ∀ i, raw37328 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37328step0 = (fun i j => raw37328 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37328step0 raw37328; decide +kernel
      have hl : raw37328step0Labels = (fun j => raw37328Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37328 raw37328Labels permutation6 hz
    mixedMoment B raw37328step0 raw37328step0Labels = mixedMoment B raw37328step1 raw37328step1Labels := by
      have ha : raw37328step1 = (fun i j => raw37328step0 (permutation661 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37328step1 raw37328step0; decide +kernel
      have hl : raw37328step1Labels = raw37328step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37328step0 raw37328step0Labels permutation661 permutation0
    mixedMoment B raw37328step1 raw37328step1Labels = mixedMoment B raw37328step2 raw37328step2Labels := by
      have ha : raw37328step2 = -raw37328step1 := by apply Matrix.ext; change ∀ i j, raw37328step2 i j = -(raw37328step1 i j); unfold raw37328step2 raw37328step1; decide +kernel
      have hl : raw37328step2Labels = raw37328step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4078 node4078Labels := by rfl

def raw37329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw37329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37329step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37329step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw37329step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37329step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw37329step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37329step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw37329step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37329 raw37329Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw37329 raw37329Labels = mixedMoment B raw37329step0 raw37329step0Labels := by
      have hz : ∀ j, raw37329 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37329step0 = (fun i j => raw37329 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37329step0 raw37329; decide +kernel
      have hl : raw37329step0Labels = raw37329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37329 raw37329Labels permutation520 hz
    mixedMoment B raw37329step0 raw37329step0Labels = mixedMoment B raw37329step1 raw37329step1Labels := by
      have hz : ∀ i, raw37329step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37329step1 = (fun i j => raw37329step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37329step1 raw37329step0; decide +kernel
      have hl : raw37329step1Labels = (fun j => raw37329step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37329step0 raw37329step0Labels permutation6 hz
    mixedMoment B raw37329step1 raw37329step1Labels = mixedMoment B raw37329step2 raw37329step2Labels := by
      have ha : raw37329step2 = (fun i j => raw37329step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37329step2 raw37329step1; decide +kernel
      have hl : raw37329step2Labels = raw37329step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37329step1 raw37329step1Labels permutation149 permutation0
    mixedMoment B raw37329step2 raw37329step2Labels = mixedMoment B raw37329step3 raw37329step3Labels := by
      have ha : raw37329step3 = -raw37329step2 := by apply Matrix.ext; change ∀ i j, raw37329step3 i j = -(raw37329step2 i j); unfold raw37329step3 raw37329step2; decide +kernel
      have hl : raw37329step3Labels = raw37329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw37330 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-3, -2, 5]]
def raw37330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![3, 2, -5], ![-3, -2, 5]]
def raw37330step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw37330step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37330 raw37330Labels = mixedMoment B node1541 node1541Labels := by
  calc
    mixedMoment B raw37330 raw37330Labels = mixedMoment B raw37330step0 raw37330step0Labels := by
      have hz : ∀ j, raw37330 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37330step0 = (fun i j => raw37330 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37330step0 raw37330; decide +kernel
      have hl : raw37330step0Labels = raw37330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37330 raw37330Labels permutation520 hz
    mixedMoment B raw37330step0 raw37330step0Labels = mixedMoment B raw37330step1 raw37330step1Labels := by
      have hz : ∀ j, raw37330step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37330step1 = (fun i j => raw37330step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37330step1 raw37330step0; decide +kernel
      have hl : raw37330step1Labels = raw37330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37330step0 raw37330step0Labels permutation104 hz
    mixedMoment B raw37330step1 raw37330step1Labels = mixedMoment B raw37330step2 raw37330step2Labels := by
      have hz : ∀ j, raw37330step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw37330step2 = (fun i j => raw37330step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw37330step2 raw37330step1; decide +kernel
      have hl : raw37330step2Labels = raw37330step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37330step1 raw37330step1Labels permutation20 hz
    mixedMoment B raw37330step2 raw37330step2Labels = mixedMoment B raw37330step3 raw37330step3Labels := by
      have hz : ∀ j, raw37330step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw37330step3 = (fun i j => raw37330step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw37330step3 raw37330step2; decide +kernel
      have hl : raw37330step3Labels = raw37330step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37330step2 raw37330step2Labels permutation4 hz
    mixedMoment B raw37330step3 raw37330step3Labels = mixedMoment B raw37330step4 raw37330step4Labels := by
      have ha : raw37330step4 = (fun i j => raw37330step3 (permutation1 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37330step4 raw37330step3; decide +kernel
      have hl : raw37330step4Labels = raw37330step3Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37330step3 raw37330step3Labels permutation1 permutation2
    _ = mixedMoment B node1541 node1541Labels := by rfl

def raw37331 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-3, -2, 5]]
def raw37331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw37331step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37331 raw37331Labels = mixedMoment B node1534 node1534Labels := by
  calc
    mixedMoment B raw37331 raw37331Labels = mixedMoment B raw37331step0 raw37331step0Labels := by
      have hz : ∀ j, raw37331 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37331step0 = (fun i j => raw37331 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37331step0 raw37331; decide +kernel
      have hl : raw37331step0Labels = raw37331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37331 raw37331Labels permutation520 hz
    mixedMoment B raw37331step0 raw37331step0Labels = mixedMoment B raw37331step1 raw37331step1Labels := by
      have hz : ∀ j, raw37331step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37331step1 = (fun i j => raw37331step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37331step1 raw37331step0; decide +kernel
      have hl : raw37331step1Labels = raw37331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37331step0 raw37331step0Labels permutation104 hz
    mixedMoment B raw37331step1 raw37331step1Labels = mixedMoment B raw37331step2 raw37331step2Labels := by
      have hz : ∀ j, raw37331step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw37331step2 = (fun i j => raw37331step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw37331step2 raw37331step1; decide +kernel
      have hl : raw37331step2Labels = raw37331step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37331step1 raw37331step1Labels permutation20 hz
    mixedMoment B raw37331step2 raw37331step2Labels = mixedMoment B raw37331step3 raw37331step3Labels := by
      have ha : raw37331step3 = (fun i j => raw37331step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37331step3 raw37331step2; decide +kernel
      have hl : raw37331step3Labels = raw37331step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37331step2 raw37331step2Labels permutation7 permutation2
    _ = mixedMoment B node1534 node1534Labels := by rfl

def raw37332 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-3, -2, 5]]
def raw37332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw37332step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37332 raw37332Labels = mixedMoment B node1534 node1534Labels := by
  calc
    mixedMoment B raw37332 raw37332Labels = mixedMoment B raw37332step0 raw37332step0Labels := by
      have hz : ∀ j, raw37332 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37332step0 = (fun i j => raw37332 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37332step0 raw37332; decide +kernel
      have hl : raw37332step0Labels = raw37332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37332 raw37332Labels permutation520 hz
    mixedMoment B raw37332step0 raw37332step0Labels = mixedMoment B raw37332step1 raw37332step1Labels := by
      have hz : ∀ j, raw37332step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37332step1 = (fun i j => raw37332step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37332step1 raw37332step0; decide +kernel
      have hl : raw37332step1Labels = raw37332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37332step0 raw37332step0Labels permutation104 hz
    mixedMoment B raw37332step1 raw37332step1Labels = mixedMoment B raw37332step2 raw37332step2Labels := by
      have hz : ∀ j, raw37332step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37332step2 = (fun i j => raw37332step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37332step2 raw37332step1; decide +kernel
      have hl : raw37332step2Labels = raw37332step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37332step1 raw37332step1Labels permutation14 hz
    mixedMoment B raw37332step2 raw37332step2Labels = mixedMoment B raw37332step3 raw37332step3Labels := by
      have ha : raw37332step3 = (fun i j => raw37332step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37332step3 raw37332step2; decide +kernel
      have hl : raw37332step3Labels = raw37332step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37332step2 raw37332step2Labels permutation7 permutation2
    _ = mixedMoment B node1534 node1534Labels := by rfl

def raw37333 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37333step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-3, -2, 5]]
def raw37333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37333step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw37333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37333 raw37333Labels = mixedMoment B node1534 node1534Labels := by
  calc
    mixedMoment B raw37333 raw37333Labels = mixedMoment B raw37333step0 raw37333step0Labels := by
      have hz : ∀ j, raw37333 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37333step0 = (fun i j => raw37333 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37333step0 raw37333; decide +kernel
      have hl : raw37333step0Labels = raw37333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37333 raw37333Labels permutation520 hz
    mixedMoment B raw37333step0 raw37333step0Labels = mixedMoment B raw37333step1 raw37333step1Labels := by
      have hz : ∀ j, raw37333step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37333step1 = (fun i j => raw37333step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37333step1 raw37333step0; decide +kernel
      have hl : raw37333step1Labels = raw37333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37333step0 raw37333step0Labels permutation80 hz
    mixedMoment B raw37333step1 raw37333step1Labels = mixedMoment B raw37333step2 raw37333step2Labels := by
      have hz : ∀ j, raw37333step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37333step2 = (fun i j => raw37333step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37333step2 raw37333step1; decide +kernel
      have hl : raw37333step2Labels = raw37333step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37333step1 raw37333step1Labels permutation14 hz
    mixedMoment B raw37333step2 raw37333step2Labels = mixedMoment B raw37333step3 raw37333step3Labels := by
      have ha : raw37333step3 = (fun i j => raw37333step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37333step3 raw37333step2; decide +kernel
      have hl : raw37333step3Labels = raw37333step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37333step2 raw37333step2Labels permutation7 permutation2
    _ = mixedMoment B node1534 node1534Labels := by rfl

def raw37334 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37334step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-3, -2, 5]]
def raw37334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37334step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw37334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37334 raw37334Labels = mixedMoment B node1534 node1534Labels := by
  calc
    mixedMoment B raw37334 raw37334Labels = mixedMoment B raw37334step0 raw37334step0Labels := by
      have hz : ∀ j, raw37334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37334step0 = (fun i j => raw37334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37334step0 raw37334; decide +kernel
      have hl : raw37334step0Labels = raw37334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37334 raw37334Labels permutation434 hz
    mixedMoment B raw37334step0 raw37334step0Labels = mixedMoment B raw37334step1 raw37334step1Labels := by
      have hz : ∀ j, raw37334step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37334step1 = (fun i j => raw37334step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37334step1 raw37334step0; decide +kernel
      have hl : raw37334step1Labels = raw37334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37334step0 raw37334step0Labels permutation80 hz
    mixedMoment B raw37334step1 raw37334step1Labels = mixedMoment B raw37334step2 raw37334step2Labels := by
      have hz : ∀ j, raw37334step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37334step2 = (fun i j => raw37334step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37334step2 raw37334step1; decide +kernel
      have hl : raw37334step2Labels = raw37334step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37334step1 raw37334step1Labels permutation14 hz
    mixedMoment B raw37334step2 raw37334step2Labels = mixedMoment B raw37334step3 raw37334step3Labels := by
      have ha : raw37334step3 = (fun i j => raw37334step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37334step3 raw37334step2; decide +kernel
      have hl : raw37334step3Labels = raw37334step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37334step2 raw37334step2Labels permutation7 permutation2
    _ = mixedMoment B node1534 node1534Labels := by rfl

def raw37335 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37335step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-2, -3, 5]]
def raw37335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37335step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 3, -5], ![-2, -3, 5]]
def raw37335step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37335step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw37335step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37335 raw37335Labels = mixedMoment B node1541 node1541Labels := by
  calc
    mixedMoment B raw37335 raw37335Labels = mixedMoment B raw37335step0 raw37335step0Labels := by
      have hz : ∀ j, raw37335 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37335step0 = (fun i j => raw37335 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37335step0 raw37335; decide +kernel
      have hl : raw37335step0Labels = raw37335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37335 raw37335Labels permutation520 hz
    mixedMoment B raw37335step0 raw37335step0Labels = mixedMoment B raw37335step1 raw37335step1Labels := by
      have hz : ∀ j, raw37335step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37335step1 = (fun i j => raw37335step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37335step1 raw37335step0; decide +kernel
      have hl : raw37335step1Labels = raw37335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37335step0 raw37335step0Labels permutation104 hz
    mixedMoment B raw37335step1 raw37335step1Labels = mixedMoment B raw37335step2 raw37335step2Labels := by
      have hz : ∀ j, raw37335step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw37335step2 = (fun i j => raw37335step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw37335step2 raw37335step1; decide +kernel
      have hl : raw37335step2Labels = raw37335step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37335step1 raw37335step1Labels permutation20 hz
    mixedMoment B raw37335step2 raw37335step2Labels = mixedMoment B raw37335step3 raw37335step3Labels := by
      have hz : ∀ j, raw37335step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw37335step3 = (fun i j => raw37335step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw37335step3 raw37335step2; decide +kernel
      have hl : raw37335step3Labels = raw37335step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37335step2 raw37335step2Labels permutation4 hz
    mixedMoment B raw37335step3 raw37335step3Labels = mixedMoment B raw37335step4 raw37335step4Labels := by
      have ha : raw37335step4 = (fun i j => raw37335step3 (permutation1 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37335step4 raw37335step3; decide +kernel
      have hl : raw37335step4Labels = raw37335step3Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37335step3 raw37335step3Labels permutation1 permutation4
    _ = mixedMoment B node1541 node1541Labels := by rfl

def raw37336 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-5, 5]]
def raw37336Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37336step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![0, 0], ![-5, 5]]
def raw37336step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37336step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![-5, 5]]
def raw37336step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37336step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![-5, 5]]
def raw37336step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37336step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![5, -5], ![-5, 5]]
def raw37336step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37336step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]
def raw37336step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37336 raw37336Labels = mixedMoment B node4062 node4062Labels := by
  calc
    mixedMoment B raw37336 raw37336Labels = mixedMoment B raw37336step0 raw37336step0Labels := by
      have hz : ∀ j, raw37336 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37336step0 = (fun i j => raw37336 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37336step0 raw37336; decide +kernel
      have hl : raw37336step0Labels = raw37336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37336 raw37336Labels permutation520 hz
    mixedMoment B raw37336step0 raw37336step0Labels = mixedMoment B raw37336step1 raw37336step1Labels := by
      have hz : ∀ j, raw37336step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37336step1 = (fun i j => raw37336step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37336step1 raw37336step0; decide +kernel
      have hl : raw37336step1Labels = raw37336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37336step0 raw37336step0Labels permutation104 hz
    mixedMoment B raw37336step1 raw37336step1Labels = mixedMoment B raw37336step2 raw37336step2Labels := by
      have hz : ∀ j, raw37336step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw37336step2 = (fun i j => raw37336step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw37336step2 raw37336step1; decide +kernel
      have hl : raw37336step2Labels = raw37336step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37336step1 raw37336step1Labels permutation20 hz
    mixedMoment B raw37336step2 raw37336step2Labels = mixedMoment B raw37336step3 raw37336step3Labels := by
      have hz : ∀ j, raw37336step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw37336step3 = (fun i j => raw37336step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw37336step3 raw37336step2; decide +kernel
      have hl : raw37336step3Labels = raw37336step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37336step2 raw37336step2Labels permutation4 hz
    mixedMoment B raw37336step3 raw37336step3Labels = mixedMoment B raw37336step4 raw37336step4Labels := by
      have ha : raw37336step4 = (fun i j => raw37336step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37336step4 raw37336step3; decide +kernel
      have hl : raw37336step4Labels = raw37336step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37336step3 raw37336step3Labels permutation1 permutation0
    _ = mixedMoment B node4062 node4062Labels := by rfl

def raw37337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37337step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-2, -3, 5]]
def raw37337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37337step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-3, -2, 5]]
def raw37337step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37337step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw37337step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37337 raw37337Labels = mixedMoment B node686 node686Labels := by
  calc
    mixedMoment B raw37337 raw37337Labels = mixedMoment B raw37337step0 raw37337step0Labels := by
      have hz : ∀ j, raw37337 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37337step0 = (fun i j => raw37337 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37337step0 raw37337; decide +kernel
      have hl : raw37337step0Labels = raw37337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37337 raw37337Labels permutation520 hz
    mixedMoment B raw37337step0 raw37337step0Labels = mixedMoment B raw37337step1 raw37337step1Labels := by
      have hz : ∀ j, raw37337step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37337step1 = (fun i j => raw37337step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37337step1 raw37337step0; decide +kernel
      have hl : raw37337step1Labels = raw37337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37337step0 raw37337step0Labels permutation104 hz
    mixedMoment B raw37337step1 raw37337step1Labels = mixedMoment B raw37337step2 raw37337step2Labels := by
      have hz : ∀ j, raw37337step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw37337step2 = (fun i j => raw37337step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw37337step2 raw37337step1; decide +kernel
      have hl : raw37337step2Labels = raw37337step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37337step1 raw37337step1Labels permutation20 hz
    mixedMoment B raw37337step2 raw37337step2Labels = mixedMoment B raw37337step3 raw37337step3Labels := by
      have ha : raw37337step3 = (fun i j => raw37337step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37337step3 raw37337step2; decide +kernel
      have hl : raw37337step3Labels = raw37337step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37337step2 raw37337step2Labels permutation2 permutation4
    mixedMoment B raw37337step3 raw37337step3Labels = mixedMoment B raw37337step4 raw37337step4Labels := by
      have ha : raw37337step4 = -raw37337step3 := by apply Matrix.ext; change ∀ i j, raw37337step4 i j = -(raw37337step3 i j); unfold raw37337step4 raw37337step3; decide +kernel
      have hl : raw37337step4Labels = raw37337step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node686 node686Labels := by rfl

def raw37338 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-2, -3, 5]]
def raw37338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37338step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-2, -3, 5]]
def raw37338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37338step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-3, -2, 5]]
def raw37338step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37338step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw37338step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37338 raw37338Labels = mixedMoment B node686 node686Labels := by
  calc
    mixedMoment B raw37338 raw37338Labels = mixedMoment B raw37338step0 raw37338step0Labels := by
      have hz : ∀ j, raw37338 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37338step0 = (fun i j => raw37338 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37338step0 raw37338; decide +kernel
      have hl : raw37338step0Labels = raw37338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37338 raw37338Labels permutation520 hz
    mixedMoment B raw37338step0 raw37338step0Labels = mixedMoment B raw37338step1 raw37338step1Labels := by
      have hz : ∀ j, raw37338step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37338step1 = (fun i j => raw37338step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37338step1 raw37338step0; decide +kernel
      have hl : raw37338step1Labels = raw37338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37338step0 raw37338step0Labels permutation104 hz
    mixedMoment B raw37338step1 raw37338step1Labels = mixedMoment B raw37338step2 raw37338step2Labels := by
      have hz : ∀ j, raw37338step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37338step2 = (fun i j => raw37338step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37338step2 raw37338step1; decide +kernel
      have hl : raw37338step2Labels = raw37338step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37338step1 raw37338step1Labels permutation14 hz
    mixedMoment B raw37338step2 raw37338step2Labels = mixedMoment B raw37338step3 raw37338step3Labels := by
      have ha : raw37338step3 = (fun i j => raw37338step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37338step3 raw37338step2; decide +kernel
      have hl : raw37338step3Labels = raw37338step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37338step2 raw37338step2Labels permutation2 permutation4
    mixedMoment B raw37338step3 raw37338step3Labels = mixedMoment B raw37338step4 raw37338step4Labels := by
      have ha : raw37338step4 = -raw37338step3 := by apply Matrix.ext; change ∀ i j, raw37338step4 i j = -(raw37338step3 i j); unfold raw37338step4 raw37338step3; decide +kernel
      have hl : raw37338step4Labels = raw37338step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node686 node686Labels := by rfl

def raw37339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -3, 5]]
def raw37339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-2, -3, 5]]
def raw37339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37339step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-2, -3, 5]]
def raw37339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37339step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-3, -2, 5]]
def raw37339step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37339step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw37339step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37339 raw37339Labels = mixedMoment B node686 node686Labels := by
  calc
    mixedMoment B raw37339 raw37339Labels = mixedMoment B raw37339step0 raw37339step0Labels := by
      have hz : ∀ j, raw37339 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37339step0 = (fun i j => raw37339 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37339step0 raw37339; decide +kernel
      have hl : raw37339step0Labels = raw37339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37339 raw37339Labels permutation520 hz
    mixedMoment B raw37339step0 raw37339step0Labels = mixedMoment B raw37339step1 raw37339step1Labels := by
      have hz : ∀ j, raw37339step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37339step1 = (fun i j => raw37339step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37339step1 raw37339step0; decide +kernel
      have hl : raw37339step1Labels = raw37339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37339step0 raw37339step0Labels permutation80 hz
    mixedMoment B raw37339step1 raw37339step1Labels = mixedMoment B raw37339step2 raw37339step2Labels := by
      have hz : ∀ j, raw37339step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37339step2 = (fun i j => raw37339step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37339step2 raw37339step1; decide +kernel
      have hl : raw37339step2Labels = raw37339step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37339step1 raw37339step1Labels permutation14 hz
    mixedMoment B raw37339step2 raw37339step2Labels = mixedMoment B raw37339step3 raw37339step3Labels := by
      have ha : raw37339step3 = (fun i j => raw37339step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37339step3 raw37339step2; decide +kernel
      have hl : raw37339step3Labels = raw37339step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37339step2 raw37339step2Labels permutation2 permutation4
    mixedMoment B raw37339step3 raw37339step3Labels = mixedMoment B raw37339step4 raw37339step4Labels := by
      have ha : raw37339step4 = -raw37339step3 := by apply Matrix.ext; change ∀ i j, raw37339step4 i j = -(raw37339step3 i j); unfold raw37339step4 raw37339step3; decide +kernel
      have hl : raw37339step4Labels = raw37339step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node686 node686Labels := by rfl

def raw37340 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -3, 5]]
def raw37340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -3, 5]]
def raw37340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-2, -3, 5]]
def raw37340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37340step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-2, -3, 5]]
def raw37340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37340step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-3, -2, 5]]
def raw37340step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37340step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw37340step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37340 raw37340Labels = mixedMoment B node686 node686Labels := by
  calc
    mixedMoment B raw37340 raw37340Labels = mixedMoment B raw37340step0 raw37340step0Labels := by
      have hz : ∀ j, raw37340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37340step0 = (fun i j => raw37340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37340step0 raw37340; decide +kernel
      have hl : raw37340step0Labels = raw37340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37340 raw37340Labels permutation434 hz
    mixedMoment B raw37340step0 raw37340step0Labels = mixedMoment B raw37340step1 raw37340step1Labels := by
      have hz : ∀ j, raw37340step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37340step1 = (fun i j => raw37340step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37340step1 raw37340step0; decide +kernel
      have hl : raw37340step1Labels = raw37340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37340step0 raw37340step0Labels permutation80 hz
    mixedMoment B raw37340step1 raw37340step1Labels = mixedMoment B raw37340step2 raw37340step2Labels := by
      have hz : ∀ j, raw37340step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37340step2 = (fun i j => raw37340step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37340step2 raw37340step1; decide +kernel
      have hl : raw37340step2Labels = raw37340step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37340step1 raw37340step1Labels permutation14 hz
    mixedMoment B raw37340step2 raw37340step2Labels = mixedMoment B raw37340step3 raw37340step3Labels := by
      have ha : raw37340step3 = (fun i j => raw37340step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37340step3 raw37340step2; decide +kernel
      have hl : raw37340step3Labels = raw37340step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37340step2 raw37340step2Labels permutation2 permutation4
    mixedMoment B raw37340step3 raw37340step3Labels = mixedMoment B raw37340step4 raw37340step4Labels := by
      have ha : raw37340step4 = -raw37340step3 := by apply Matrix.ext; change ∀ i j, raw37340step4 i j = -(raw37340step3 i j); unfold raw37340step4 raw37340step3; decide +kernel
      have hl : raw37340step4Labels = raw37340step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node686 node686Labels := by rfl

def raw37341 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -4, 5]]
def raw37341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -4, 5]]
def raw37341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![-1, -4, 5]]
def raw37341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37341step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![-1, -4, 5]]
def raw37341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37341step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 4, -5], ![-1, -4, 5]]
def raw37341step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37341step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, -1, 5], ![4, 1, -5]]
def raw37341step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37341 raw37341Labels = mixedMoment B node697 node697Labels := by
  calc
    mixedMoment B raw37341 raw37341Labels = mixedMoment B raw37341step0 raw37341step0Labels := by
      have hz : ∀ j, raw37341 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37341step0 = (fun i j => raw37341 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37341step0 raw37341; decide +kernel
      have hl : raw37341step0Labels = raw37341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37341 raw37341Labels permutation520 hz
    mixedMoment B raw37341step0 raw37341step0Labels = mixedMoment B raw37341step1 raw37341step1Labels := by
      have hz : ∀ j, raw37341step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw37341step1 = (fun i j => raw37341step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw37341step1 raw37341step0; decide +kernel
      have hl : raw37341step1Labels = raw37341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37341step0 raw37341step0Labels permutation104 hz
    mixedMoment B raw37341step1 raw37341step1Labels = mixedMoment B raw37341step2 raw37341step2Labels := by
      have hz : ∀ j, raw37341step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw37341step2 = (fun i j => raw37341step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw37341step2 raw37341step1; decide +kernel
      have hl : raw37341step2Labels = raw37341step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37341step1 raw37341step1Labels permutation20 hz
    mixedMoment B raw37341step2 raw37341step2Labels = mixedMoment B raw37341step3 raw37341step3Labels := by
      have hz : ∀ j, raw37341step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw37341step3 = (fun i j => raw37341step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw37341step3 raw37341step2; decide +kernel
      have hl : raw37341step3Labels = raw37341step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37341step2 raw37341step2Labels permutation4 hz
    mixedMoment B raw37341step3 raw37341step3Labels = mixedMoment B raw37341step4 raw37341step4Labels := by
      have ha : raw37341step4 = (fun i j => raw37341step3 (permutation1 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37341step4 raw37341step3; decide +kernel
      have hl : raw37341step4Labels = raw37341step3Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37341step3 raw37341step3Labels permutation1 permutation4
    _ = mixedMoment B node697 node697Labels := by rfl

def raw37342 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37342step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw37342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37342step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw37342step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37342 raw37342Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw37342 raw37342Labels = mixedMoment B raw37342step0 raw37342step0Labels := by
      have hz : ∀ j, raw37342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37342step0 = (fun i j => raw37342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37342step0 raw37342; decide +kernel
      have hl : raw37342step0Labels = raw37342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37342 raw37342Labels permutation434 hz
    mixedMoment B raw37342step0 raw37342step0Labels = mixedMoment B raw37342step1 raw37342step1Labels := by
      have hz : ∀ j, raw37342step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37342step1 = (fun i j => raw37342step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37342step1 raw37342step0; decide +kernel
      have hl : raw37342step1Labels = raw37342step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37342step0 raw37342step0Labels permutation80 hz
    mixedMoment B raw37342step1 raw37342step1Labels = mixedMoment B raw37342step2 raw37342step2Labels := by
      have hz : ∀ j, raw37342step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37342step2 = (fun i j => raw37342step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37342step2 raw37342step1; decide +kernel
      have hl : raw37342step2Labels = raw37342step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37342step1 raw37342step1Labels permutation14 hz
    mixedMoment B raw37342step2 raw37342step2Labels = mixedMoment B raw37342step3 raw37342step3Labels := by
      have ha : raw37342step3 = -raw37342step2 := by apply Matrix.ext; change ∀ i j, raw37342step3 i j = -(raw37342step2 i j); unfold raw37342step3 raw37342step2; decide +kernel
      have hl : raw37342step3Labels = raw37342step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1521 node1521Labels := by rfl

def raw37343 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37343step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37343step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37343step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37343step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw37343step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37343 raw37343Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw37343 raw37343Labels = mixedMoment B raw37343step0 raw37343step0Labels := by
      have hz : ∀ j, raw37343 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37343step0 = (fun i j => raw37343 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37343step0 raw37343; decide +kernel
      have hl : raw37343step0Labels = raw37343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37343 raw37343Labels permutation434 hz
    mixedMoment B raw37343step0 raw37343step0Labels = mixedMoment B raw37343step1 raw37343step1Labels := by
      have hz : ∀ j, raw37343step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37343step1 = (fun i j => raw37343step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37343step1 raw37343step0; decide +kernel
      have hl : raw37343step1Labels = raw37343step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37343step0 raw37343step0Labels permutation80 hz
    mixedMoment B raw37343step1 raw37343step1Labels = mixedMoment B raw37343step2 raw37343step2Labels := by
      have ha : raw37343step2 = (fun i j => raw37343step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37343step2 raw37343step1; decide +kernel
      have hl : raw37343step2Labels = raw37343step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37343step1 raw37343step1Labels permutation8 permutation4
    mixedMoment B raw37343step2 raw37343step2Labels = mixedMoment B raw37343step3 raw37343step3Labels := by
      have ha : raw37343step3 = -raw37343step2 := by apply Matrix.ext; change ∀ i j, raw37343step3 i j = -(raw37343step2 i j); unfold raw37343step3 raw37343step2; decide +kernel
      have hl : raw37343step3Labels = raw37343step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1532 node1532Labels := by rfl

def raw37344 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37344step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37344step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw37344step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37344 raw37344Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw37344 raw37344Labels = mixedMoment B raw37344step0 raw37344step0Labels := by
      have hz : ∀ j, raw37344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37344step0 = (fun i j => raw37344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37344step0 raw37344; decide +kernel
      have hl : raw37344step0Labels = raw37344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37344 raw37344Labels permutation434 hz
    mixedMoment B raw37344step0 raw37344step0Labels = mixedMoment B raw37344step1 raw37344step1Labels := by
      have hz : ∀ j, raw37344step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37344step1 = (fun i j => raw37344step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37344step1 raw37344step0; decide +kernel
      have hl : raw37344step1Labels = raw37344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37344step0 raw37344step0Labels permutation56 hz
    mixedMoment B raw37344step1 raw37344step1Labels = mixedMoment B raw37344step2 raw37344step2Labels := by
      have ha : raw37344step2 = (fun i j => raw37344step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37344step2 raw37344step1; decide +kernel
      have hl : raw37344step2Labels = raw37344step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37344step1 raw37344step1Labels permutation8 permutation4
    mixedMoment B raw37344step2 raw37344step2Labels = mixedMoment B raw37344step3 raw37344step3Labels := by
      have ha : raw37344step3 = -raw37344step2 := by apply Matrix.ext; change ∀ i j, raw37344step3 i j = -(raw37344step2 i j); unfold raw37344step3 raw37344step2; decide +kernel
      have hl : raw37344step3Labels = raw37344step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1532 node1532Labels := by rfl

def raw37345 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37345step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37345step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw37345step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37345 raw37345Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw37345 raw37345Labels = mixedMoment B raw37345step0 raw37345step0Labels := by
      have hz : ∀ j, raw37345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37345step0 = (fun i j => raw37345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37345step0 raw37345; decide +kernel
      have hl : raw37345step0Labels = raw37345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37345 raw37345Labels permutation346 hz
    mixedMoment B raw37345step0 raw37345step0Labels = mixedMoment B raw37345step1 raw37345step1Labels := by
      have hz : ∀ j, raw37345step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37345step1 = (fun i j => raw37345step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37345step1 raw37345step0; decide +kernel
      have hl : raw37345step1Labels = raw37345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37345step0 raw37345step0Labels permutation56 hz
    mixedMoment B raw37345step1 raw37345step1Labels = mixedMoment B raw37345step2 raw37345step2Labels := by
      have ha : raw37345step2 = (fun i j => raw37345step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37345step2 raw37345step1; decide +kernel
      have hl : raw37345step2Labels = raw37345step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37345step1 raw37345step1Labels permutation8 permutation4
    mixedMoment B raw37345step2 raw37345step2Labels = mixedMoment B raw37345step3 raw37345step3Labels := by
      have ha : raw37345step3 = -raw37345step2 := by apply Matrix.ext; change ∀ i j, raw37345step3 i j = -(raw37345step2 i j); unfold raw37345step3 raw37345step2; decide +kernel
      have hl : raw37345step3Labels = raw37345step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1532 node1532Labels := by rfl

def raw37346 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, -1, 4]]
def raw37346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, -1, 4]]
def raw37346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -2, 1], ![-3, -1, 4]]
def raw37346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37346step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -2, 1], ![-3, -1, 4]]
def raw37346step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37346step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -3, 4], ![-2, 1, 1]]
def raw37346step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37346step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw37346step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37346 raw37346Labels = mixedMoment B node1540 node1540Labels := by
  calc
    mixedMoment B raw37346 raw37346Labels = mixedMoment B raw37346step0 raw37346step0Labels := by
      have hz : ∀ j, raw37346 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37346step0 = (fun i j => raw37346 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37346step0 raw37346; decide +kernel
      have hl : raw37346step0Labels = raw37346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37346 raw37346Labels permutation434 hz
    mixedMoment B raw37346step0 raw37346step0Labels = mixedMoment B raw37346step1 raw37346step1Labels := by
      have hz : ∀ j, raw37346step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37346step1 = (fun i j => raw37346step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37346step1 raw37346step0; decide +kernel
      have hl : raw37346step1Labels = raw37346step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37346step0 raw37346step0Labels permutation80 hz
    mixedMoment B raw37346step1 raw37346step1Labels = mixedMoment B raw37346step2 raw37346step2Labels := by
      have hz : ∀ j, raw37346step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37346step2 = (fun i j => raw37346step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37346step2 raw37346step1; decide +kernel
      have hl : raw37346step2Labels = raw37346step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37346step1 raw37346step1Labels permutation14 hz
    mixedMoment B raw37346step2 raw37346step2Labels = mixedMoment B raw37346step3 raw37346step3Labels := by
      have ha : raw37346step3 = (fun i j => raw37346step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37346step3 raw37346step2; decide +kernel
      have hl : raw37346step3Labels = raw37346step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37346step2 raw37346step2Labels permutation3 permutation4
    mixedMoment B raw37346step3 raw37346step3Labels = mixedMoment B raw37346step4 raw37346step4Labels := by
      have ha : raw37346step4 = -raw37346step3 := by apply Matrix.ext; change ∀ i j, raw37346step4 i j = -(raw37346step3 i j); unfold raw37346step4 raw37346step3; decide +kernel
      have hl : raw37346step4Labels = raw37346step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1540 node1540Labels := by rfl

def raw37347 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37347step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-2, -2, 4]]
def raw37347step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37347step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-2, -2, 4]]
def raw37347step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37347step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw37347step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37347 raw37347Labels = mixedMoment B node1537 node1537Labels := by
  calc
    mixedMoment B raw37347 raw37347Labels = mixedMoment B raw37347step0 raw37347step0Labels := by
      have hz : ∀ j, raw37347 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37347step0 = (fun i j => raw37347 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37347step0 raw37347; decide +kernel
      have hl : raw37347step0Labels = raw37347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37347 raw37347Labels permutation434 hz
    mixedMoment B raw37347step0 raw37347step0Labels = mixedMoment B raw37347step1 raw37347step1Labels := by
      have hz : ∀ j, raw37347step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37347step1 = (fun i j => raw37347step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37347step1 raw37347step0; decide +kernel
      have hl : raw37347step1Labels = raw37347step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37347step0 raw37347step0Labels permutation80 hz
    mixedMoment B raw37347step1 raw37347step1Labels = mixedMoment B raw37347step2 raw37347step2Labels := by
      have hz : ∀ j, raw37347step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37347step2 = (fun i j => raw37347step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37347step2 raw37347step1; decide +kernel
      have hl : raw37347step2Labels = raw37347step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37347step1 raw37347step1Labels permutation14 hz
    mixedMoment B raw37347step2 raw37347step2Labels = mixedMoment B raw37347step3 raw37347step3Labels := by
      have ha : raw37347step3 = (fun i j => raw37347step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37347step3 raw37347step2; decide +kernel
      have hl : raw37347step3Labels = raw37347step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37347step2 raw37347step2Labels permutation2 permutation4
    mixedMoment B raw37347step3 raw37347step3Labels = mixedMoment B raw37347step4 raw37347step4Labels := by
      have ha : raw37347step4 = -raw37347step3 := by apply Matrix.ext; change ∀ i j, raw37347step4 i j = -(raw37347step3 i j); unfold raw37347step4 raw37347step3; decide +kernel
      have hl : raw37347step4Labels = raw37347step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1537 node1537Labels := by rfl

def raw37348 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![-4, 4]]
def raw37348Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37348step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![-1, 1], ![-4, 4]]
def raw37348step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37348step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![-1, 1], ![-4, 4]]
def raw37348step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37348step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-4, 4]]
def raw37348step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37348step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw37348step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37348 raw37348Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw37348 raw37348Labels = mixedMoment B raw37348step0 raw37348step0Labels := by
      have hz : ∀ j, raw37348 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37348step0 = (fun i j => raw37348 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37348step0 raw37348; decide +kernel
      have hl : raw37348step0Labels = raw37348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37348 raw37348Labels permutation434 hz
    mixedMoment B raw37348step0 raw37348step0Labels = mixedMoment B raw37348step1 raw37348step1Labels := by
      have hz : ∀ j, raw37348step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37348step1 = (fun i j => raw37348step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37348step1 raw37348step0; decide +kernel
      have hl : raw37348step1Labels = raw37348step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37348step0 raw37348step0Labels permutation80 hz
    mixedMoment B raw37348step1 raw37348step1Labels = mixedMoment B raw37348step2 raw37348step2Labels := by
      have hz : ∀ j, raw37348step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37348step2 = (fun i j => raw37348step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37348step2 raw37348step1; decide +kernel
      have hl : raw37348step2Labels = raw37348step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37348step1 raw37348step1Labels permutation14 hz
    mixedMoment B raw37348step2 raw37348step2Labels = mixedMoment B raw37348step3 raw37348step3Labels := by
      have ha : raw37348step3 = -raw37348step2 := by apply Matrix.ext; change ∀ i j, raw37348step3 i j = -(raw37348step2 i j); unfold raw37348step3 raw37348step2; decide +kernel
      have hl : raw37348step3Labels = raw37348step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4060 node4060Labels := by rfl

def raw37349 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37349step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-2, -2, 4]]
def raw37349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37349step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw37349step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37349 raw37349Labels = mixedMoment B node1537 node1537Labels := by
  calc
    mixedMoment B raw37349 raw37349Labels = mixedMoment B raw37349step0 raw37349step0Labels := by
      have hz : ∀ j, raw37349 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37349step0 = (fun i j => raw37349 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37349step0 raw37349; decide +kernel
      have hl : raw37349step0Labels = raw37349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37349 raw37349Labels permutation434 hz
    mixedMoment B raw37349step0 raw37349step0Labels = mixedMoment B raw37349step1 raw37349step1Labels := by
      have hz : ∀ j, raw37349step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37349step1 = (fun i j => raw37349step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37349step1 raw37349step0; decide +kernel
      have hl : raw37349step1Labels = raw37349step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37349step0 raw37349step0Labels permutation80 hz
    mixedMoment B raw37349step1 raw37349step1Labels = mixedMoment B raw37349step2 raw37349step2Labels := by
      have hz : ∀ j, raw37349step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37349step2 = (fun i j => raw37349step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37349step2 raw37349step1; decide +kernel
      have hl : raw37349step2Labels = raw37349step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37349step1 raw37349step1Labels permutation14 hz
    mixedMoment B raw37349step2 raw37349step2Labels = mixedMoment B raw37349step3 raw37349step3Labels := by
      have ha : raw37349step3 = -raw37349step2 := by apply Matrix.ext; change ∀ i j, raw37349step3 i j = -(raw37349step2 i j); unfold raw37349step3 raw37349step2; decide +kernel
      have hl : raw37349step3Labels = raw37349step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1537 node1537Labels := by rfl

def raw37350 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw37350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37350step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37350 raw37350Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw37350 raw37350Labels = mixedMoment B raw37350step0 raw37350step0Labels := by
      have hz : ∀ j, raw37350 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37350step0 = (fun i j => raw37350 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37350step0 raw37350; decide +kernel
      have hl : raw37350step0Labels = raw37350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37350 raw37350Labels permutation434 hz
    mixedMoment B raw37350step0 raw37350step0Labels = mixedMoment B raw37350step1 raw37350step1Labels := by
      have hz : ∀ j, raw37350step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37350step1 = (fun i j => raw37350step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37350step1 raw37350step0; decide +kernel
      have hl : raw37350step1Labels = raw37350step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37350step0 raw37350step0Labels permutation80 hz
    mixedMoment B raw37350step1 raw37350step1Labels = mixedMoment B raw37350step2 raw37350step2Labels := by
      have ha : raw37350step2 = (fun i j => raw37350step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37350step2 raw37350step1; decide +kernel
      have hl : raw37350step2Labels = raw37350step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37350step1 raw37350step1Labels permutation10 permutation4
    mixedMoment B raw37350step2 raw37350step2Labels = mixedMoment B raw37350step3 raw37350step3Labels := by
      have ha : raw37350step3 = -raw37350step2 := by apply Matrix.ext; change ∀ i j, raw37350step3 i j = -(raw37350step2 i j); unfold raw37350step3 raw37350step2; decide +kernel
      have hl : raw37350step3Labels = raw37350step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1516 node1516Labels := by rfl

def raw37351 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37351step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37351step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw37351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37351step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37351step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37351 raw37351Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw37351 raw37351Labels = mixedMoment B raw37351step0 raw37351step0Labels := by
      have hz : ∀ j, raw37351 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37351step0 = (fun i j => raw37351 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37351step0 raw37351; decide +kernel
      have hl : raw37351step0Labels = raw37351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37351 raw37351Labels permutation434 hz
    mixedMoment B raw37351step0 raw37351step0Labels = mixedMoment B raw37351step1 raw37351step1Labels := by
      have hz : ∀ j, raw37351step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37351step1 = (fun i j => raw37351step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37351step1 raw37351step0; decide +kernel
      have hl : raw37351step1Labels = raw37351step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37351step0 raw37351step0Labels permutation56 hz
    mixedMoment B raw37351step1 raw37351step1Labels = mixedMoment B raw37351step2 raw37351step2Labels := by
      have ha : raw37351step2 = (fun i j => raw37351step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37351step2 raw37351step1; decide +kernel
      have hl : raw37351step2Labels = raw37351step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37351step1 raw37351step1Labels permutation10 permutation4
    mixedMoment B raw37351step2 raw37351step2Labels = mixedMoment B raw37351step3 raw37351step3Labels := by
      have ha : raw37351step3 = -raw37351step2 := by apply Matrix.ext; change ∀ i j, raw37351step3 i j = -(raw37351step2 i j); unfold raw37351step3 raw37351step2; decide +kernel
      have hl : raw37351step3Labels = raw37351step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1516 node1516Labels := by rfl

def raw37352 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw37352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37352step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37352step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37352 raw37352Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw37352 raw37352Labels = mixedMoment B raw37352step0 raw37352step0Labels := by
      have hz : ∀ j, raw37352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37352step0 = (fun i j => raw37352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37352step0 raw37352; decide +kernel
      have hl : raw37352step0Labels = raw37352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37352 raw37352Labels permutation346 hz
    mixedMoment B raw37352step0 raw37352step0Labels = mixedMoment B raw37352step1 raw37352step1Labels := by
      have hz : ∀ j, raw37352step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37352step1 = (fun i j => raw37352step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37352step1 raw37352step0; decide +kernel
      have hl : raw37352step1Labels = raw37352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37352step0 raw37352step0Labels permutation56 hz
    mixedMoment B raw37352step1 raw37352step1Labels = mixedMoment B raw37352step2 raw37352step2Labels := by
      have ha : raw37352step2 = (fun i j => raw37352step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37352step2 raw37352step1; decide +kernel
      have hl : raw37352step2Labels = raw37352step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37352step1 raw37352step1Labels permutation10 permutation4
    mixedMoment B raw37352step2 raw37352step2Labels = mixedMoment B raw37352step3 raw37352step3Labels := by
      have ha : raw37352step3 = -raw37352step2 := by apply Matrix.ext; change ∀ i j, raw37352step3 i j = -(raw37352step2 i j); unfold raw37352step3 raw37352step2; decide +kernel
      have hl : raw37352step3Labels = raw37352step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1516 node1516Labels := by rfl

def raw37353 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37353step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, -3, 4]]
def raw37353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37353step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw37353step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37353step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw37353step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37353 raw37353Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw37353 raw37353Labels = mixedMoment B raw37353step0 raw37353step0Labels := by
      have hz : ∀ j, raw37353 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37353step0 = (fun i j => raw37353 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37353step0 raw37353; decide +kernel
      have hl : raw37353step0Labels = raw37353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37353 raw37353Labels permutation434 hz
    mixedMoment B raw37353step0 raw37353step0Labels = mixedMoment B raw37353step1 raw37353step1Labels := by
      have hz : ∀ j, raw37353step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37353step1 = (fun i j => raw37353step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37353step1 raw37353step0; decide +kernel
      have hl : raw37353step1Labels = raw37353step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37353step0 raw37353step0Labels permutation80 hz
    mixedMoment B raw37353step1 raw37353step1Labels = mixedMoment B raw37353step2 raw37353step2Labels := by
      have hz : ∀ j, raw37353step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37353step2 = (fun i j => raw37353step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37353step2 raw37353step1; decide +kernel
      have hl : raw37353step2Labels = raw37353step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37353step1 raw37353step1Labels permutation14 hz
    mixedMoment B raw37353step2 raw37353step2Labels = mixedMoment B raw37353step3 raw37353step3Labels := by
      have ha : raw37353step3 = (fun i j => raw37353step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37353step3 raw37353step2; decide +kernel
      have hl : raw37353step3Labels = raw37353step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37353step2 raw37353step2Labels permutation2 permutation4
    mixedMoment B raw37353step3 raw37353step3Labels = mixedMoment B raw37353step4 raw37353step4Labels := by
      have ha : raw37353step4 = -raw37353step3 := by apply Matrix.ext; change ∀ i j, raw37353step4 i j = -(raw37353step3 i j); unfold raw37353step4 raw37353step3; decide +kernel
      have hl : raw37353step4Labels = raw37353step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1521 node1521Labels := by rfl

def raw37354 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37354step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw37354step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37354 raw37354Labels = mixedMoment B node683 node683Labels := by
  calc
    mixedMoment B raw37354 raw37354Labels = mixedMoment B raw37354step0 raw37354step0Labels := by
      have hz : ∀ j, raw37354 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37354step0 = (fun i j => raw37354 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37354step0 raw37354; decide +kernel
      have hl : raw37354step0Labels = raw37354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37354 raw37354Labels permutation434 hz
    mixedMoment B raw37354step0 raw37354step0Labels = mixedMoment B raw37354step1 raw37354step1Labels := by
      have hz : ∀ j, raw37354step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37354step1 = (fun i j => raw37354step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37354step1 raw37354step0; decide +kernel
      have hl : raw37354step1Labels = raw37354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37354step0 raw37354step0Labels permutation80 hz
    mixedMoment B raw37354step1 raw37354step1Labels = mixedMoment B raw37354step2 raw37354step2Labels := by
      have ha : raw37354step2 = (fun i j => raw37354step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37354step2 raw37354step1; decide +kernel
      have hl : raw37354step2Labels = raw37354step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37354step1 raw37354step1Labels permutation8 permutation4
    mixedMoment B raw37354step2 raw37354step2Labels = mixedMoment B raw37354step3 raw37354step3Labels := by
      have ha : raw37354step3 = -raw37354step2 := by apply Matrix.ext; change ∀ i j, raw37354step3 i j = -(raw37354step2 i j); unfold raw37354step3 raw37354step2; decide +kernel
      have hl : raw37354step3Labels = raw37354step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node683 node683Labels := by rfl

def raw37355 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37355step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw37355step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37355 raw37355Labels = mixedMoment B node683 node683Labels := by
  calc
    mixedMoment B raw37355 raw37355Labels = mixedMoment B raw37355step0 raw37355step0Labels := by
      have hz : ∀ j, raw37355 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37355step0 = (fun i j => raw37355 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37355step0 raw37355; decide +kernel
      have hl : raw37355step0Labels = raw37355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37355 raw37355Labels permutation434 hz
    mixedMoment B raw37355step0 raw37355step0Labels = mixedMoment B raw37355step1 raw37355step1Labels := by
      have hz : ∀ j, raw37355step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37355step1 = (fun i j => raw37355step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37355step1 raw37355step0; decide +kernel
      have hl : raw37355step1Labels = raw37355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37355step0 raw37355step0Labels permutation56 hz
    mixedMoment B raw37355step1 raw37355step1Labels = mixedMoment B raw37355step2 raw37355step2Labels := by
      have ha : raw37355step2 = (fun i j => raw37355step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37355step2 raw37355step1; decide +kernel
      have hl : raw37355step2Labels = raw37355step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37355step1 raw37355step1Labels permutation8 permutation4
    mixedMoment B raw37355step2 raw37355step2Labels = mixedMoment B raw37355step3 raw37355step3Labels := by
      have ha : raw37355step3 = -raw37355step2 := by apply Matrix.ext; change ∀ i j, raw37355step3 i j = -(raw37355step2 i j); unfold raw37355step3 raw37355step2; decide +kernel
      have hl : raw37355step3Labels = raw37355step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node683 node683Labels := by rfl

def raw37356 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37356step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37356step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw37356step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37356 raw37356Labels = mixedMoment B node683 node683Labels := by
  calc
    mixedMoment B raw37356 raw37356Labels = mixedMoment B raw37356step0 raw37356step0Labels := by
      have hz : ∀ j, raw37356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37356step0 = (fun i j => raw37356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37356step0 raw37356; decide +kernel
      have hl : raw37356step0Labels = raw37356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37356 raw37356Labels permutation346 hz
    mixedMoment B raw37356step0 raw37356step0Labels = mixedMoment B raw37356step1 raw37356step1Labels := by
      have hz : ∀ j, raw37356step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37356step1 = (fun i j => raw37356step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37356step1 raw37356step0; decide +kernel
      have hl : raw37356step1Labels = raw37356step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37356step0 raw37356step0Labels permutation56 hz
    mixedMoment B raw37356step1 raw37356step1Labels = mixedMoment B raw37356step2 raw37356step2Labels := by
      have ha : raw37356step2 = (fun i j => raw37356step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37356step2 raw37356step1; decide +kernel
      have hl : raw37356step2Labels = raw37356step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37356step1 raw37356step1Labels permutation8 permutation4
    mixedMoment B raw37356step2 raw37356step2Labels = mixedMoment B raw37356step3 raw37356step3Labels := by
      have ha : raw37356step3 = -raw37356step2 := by apply Matrix.ext; change ∀ i j, raw37356step3 i j = -(raw37356step2 i j); unfold raw37356step3 raw37356step2; decide +kernel
      have hl : raw37356step3Labels = raw37356step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node683 node683Labels := by rfl

def raw37357 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -2, 4]]
def raw37357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -2, 4]]
def raw37357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -2, 1], ![-2, -2, 4]]
def raw37357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37357step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![-2, -2, 4]]
def raw37357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37357step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-2, 1, 1], ![-2, -2, 4]]
def raw37357step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37357step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, -1, -1], ![2, 2, -4]]
def raw37357step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37357 raw37357Labels = mixedMoment B node695 node695Labels := by
  calc
    mixedMoment B raw37357 raw37357Labels = mixedMoment B raw37357step0 raw37357step0Labels := by
      have hz : ∀ j, raw37357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37357step0 = (fun i j => raw37357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37357step0 raw37357; decide +kernel
      have hl : raw37357step0Labels = raw37357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37357 raw37357Labels permutation434 hz
    mixedMoment B raw37357step0 raw37357step0Labels = mixedMoment B raw37357step1 raw37357step1Labels := by
      have hz : ∀ j, raw37357step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37357step1 = (fun i j => raw37357step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37357step1 raw37357step0; decide +kernel
      have hl : raw37357step1Labels = raw37357step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37357step0 raw37357step0Labels permutation80 hz
    mixedMoment B raw37357step1 raw37357step1Labels = mixedMoment B raw37357step2 raw37357step2Labels := by
      have hz : ∀ j, raw37357step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37357step2 = (fun i j => raw37357step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37357step2 raw37357step1; decide +kernel
      have hl : raw37357step2Labels = raw37357step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37357step1 raw37357step1Labels permutation14 hz
    mixedMoment B raw37357step2 raw37357step2Labels = mixedMoment B raw37357step3 raw37357step3Labels := by
      have ha : raw37357step3 = (fun i j => raw37357step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37357step3 raw37357step2; decide +kernel
      have hl : raw37357step3Labels = raw37357step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37357step2 raw37357step2Labels permutation2 permutation4
    mixedMoment B raw37357step3 raw37357step3Labels = mixedMoment B raw37357step4 raw37357step4Labels := by
      have ha : raw37357step4 = -raw37357step3 := by apply Matrix.ext; change ∀ i j, raw37357step4 i j = -(raw37357step3 i j); unfold raw37357step4 raw37357step3; decide +kernel
      have hl : raw37357step4Labels = raw37357step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node695 node695Labels := by rfl

def raw37358 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37358step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![-1, -3, 4]]
def raw37358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37358step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-3, -1, 4]]
def raw37358step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37358step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![3, 1, -4]]
def raw37358step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37358 raw37358Labels = mixedMoment B node691 node691Labels := by
  calc
    mixedMoment B raw37358 raw37358Labels = mixedMoment B raw37358step0 raw37358step0Labels := by
      have hz : ∀ j, raw37358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37358step0 = (fun i j => raw37358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37358step0 raw37358; decide +kernel
      have hl : raw37358step0Labels = raw37358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37358 raw37358Labels permutation434 hz
    mixedMoment B raw37358step0 raw37358step0Labels = mixedMoment B raw37358step1 raw37358step1Labels := by
      have hz : ∀ j, raw37358step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37358step1 = (fun i j => raw37358step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37358step1 raw37358step0; decide +kernel
      have hl : raw37358step1Labels = raw37358step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37358step0 raw37358step0Labels permutation80 hz
    mixedMoment B raw37358step1 raw37358step1Labels = mixedMoment B raw37358step2 raw37358step2Labels := by
      have hz : ∀ j, raw37358step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37358step2 = (fun i j => raw37358step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37358step2 raw37358step1; decide +kernel
      have hl : raw37358step2Labels = raw37358step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37358step1 raw37358step1Labels permutation14 hz
    mixedMoment B raw37358step2 raw37358step2Labels = mixedMoment B raw37358step3 raw37358step3Labels := by
      have ha : raw37358step3 = (fun i j => raw37358step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37358step3 raw37358step2; decide +kernel
      have hl : raw37358step3Labels = raw37358step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37358step2 raw37358step2Labels permutation2 permutation4
    mixedMoment B raw37358step3 raw37358step3Labels = mixedMoment B raw37358step4 raw37358step4Labels := by
      have ha : raw37358step4 = -raw37358step3 := by apply Matrix.ext; change ∀ i j, raw37358step4 i j = -(raw37358step3 i j); unfold raw37358step4 raw37358step3; decide +kernel
      have hl : raw37358step4Labels = raw37358step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node691 node691Labels := by rfl

def raw37359 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-3, -1, 4]]
def raw37359step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37359step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw37359step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37359 raw37359Labels = mixedMoment B node1494 node1494Labels := by
  calc
    mixedMoment B raw37359 raw37359Labels = mixedMoment B raw37359step0 raw37359step0Labels := by
      have hz : ∀ j, raw37359 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37359step0 = (fun i j => raw37359 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37359step0 raw37359; decide +kernel
      have hl : raw37359step0Labels = raw37359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37359 raw37359Labels permutation434 hz
    mixedMoment B raw37359step0 raw37359step0Labels = mixedMoment B raw37359step1 raw37359step1Labels := by
      have hz : ∀ j, raw37359step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37359step1 = (fun i j => raw37359step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37359step1 raw37359step0; decide +kernel
      have hl : raw37359step1Labels = raw37359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37359step0 raw37359step0Labels permutation80 hz
    mixedMoment B raw37359step1 raw37359step1Labels = mixedMoment B raw37359step2 raw37359step2Labels := by
      have ha : raw37359step2 = (fun i j => raw37359step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37359step2 raw37359step1; decide +kernel
      have hl : raw37359step2Labels = raw37359step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37359step1 raw37359step1Labels permutation8 permutation4
    mixedMoment B raw37359step2 raw37359step2Labels = mixedMoment B raw37359step3 raw37359step3Labels := by
      have ha : raw37359step3 = -raw37359step2 := by apply Matrix.ext; change ∀ i j, raw37359step3 i j = -(raw37359step2 i j); unfold raw37359step3 raw37359step2; decide +kernel
      have hl : raw37359step3Labels = raw37359step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1494 node1494Labels := by rfl

def raw37360 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37360step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37360step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-3, -1, 4]]
def raw37360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37360step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw37360step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37360 raw37360Labels = mixedMoment B node1494 node1494Labels := by
  calc
    mixedMoment B raw37360 raw37360Labels = mixedMoment B raw37360step0 raw37360step0Labels := by
      have hz : ∀ j, raw37360 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37360step0 = (fun i j => raw37360 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37360step0 raw37360; decide +kernel
      have hl : raw37360step0Labels = raw37360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37360 raw37360Labels permutation434 hz
    mixedMoment B raw37360step0 raw37360step0Labels = mixedMoment B raw37360step1 raw37360step1Labels := by
      have hz : ∀ j, raw37360step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37360step1 = (fun i j => raw37360step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37360step1 raw37360step0; decide +kernel
      have hl : raw37360step1Labels = raw37360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37360step0 raw37360step0Labels permutation56 hz
    mixedMoment B raw37360step1 raw37360step1Labels = mixedMoment B raw37360step2 raw37360step2Labels := by
      have ha : raw37360step2 = (fun i j => raw37360step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37360step2 raw37360step1; decide +kernel
      have hl : raw37360step2Labels = raw37360step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37360step1 raw37360step1Labels permutation8 permutation4
    mixedMoment B raw37360step2 raw37360step2Labels = mixedMoment B raw37360step3 raw37360step3Labels := by
      have ha : raw37360step3 = -raw37360step2 := by apply Matrix.ext; change ∀ i j, raw37360step3 i j = -(raw37360step2 i j); unfold raw37360step3 raw37360step2; decide +kernel
      have hl : raw37360step3Labels = raw37360step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1494 node1494Labels := by rfl

def raw37361 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-3, -1, 4]]
def raw37361step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37361step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw37361step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37361 raw37361Labels = mixedMoment B node1494 node1494Labels := by
  calc
    mixedMoment B raw37361 raw37361Labels = mixedMoment B raw37361step0 raw37361step0Labels := by
      have hz : ∀ j, raw37361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37361step0 = (fun i j => raw37361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37361step0 raw37361; decide +kernel
      have hl : raw37361step0Labels = raw37361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37361 raw37361Labels permutation346 hz
    mixedMoment B raw37361step0 raw37361step0Labels = mixedMoment B raw37361step1 raw37361step1Labels := by
      have hz : ∀ j, raw37361step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37361step1 = (fun i j => raw37361step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37361step1 raw37361step0; decide +kernel
      have hl : raw37361step1Labels = raw37361step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37361step0 raw37361step0Labels permutation56 hz
    mixedMoment B raw37361step1 raw37361step1Labels = mixedMoment B raw37361step2 raw37361step2Labels := by
      have ha : raw37361step2 = (fun i j => raw37361step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37361step2 raw37361step1; decide +kernel
      have hl : raw37361step2Labels = raw37361step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37361step1 raw37361step1Labels permutation8 permutation4
    mixedMoment B raw37361step2 raw37361step2Labels = mixedMoment B raw37361step3 raw37361step3Labels := by
      have ha : raw37361step3 = -raw37361step2 := by apply Matrix.ext; change ∀ i j, raw37361step3 i j = -(raw37361step2 i j); unfold raw37361step3 raw37361step2; decide +kernel
      have hl : raw37361step3Labels = raw37361step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1494 node1494Labels := by rfl

def raw37362 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw37362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37362step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw37362step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37362 raw37362Labels = mixedMoment B node665 node665Labels := by
  calc
    mixedMoment B raw37362 raw37362Labels = mixedMoment B raw37362step0 raw37362step0Labels := by
      have hz : ∀ j, raw37362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37362step0 = (fun i j => raw37362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37362step0 raw37362; decide +kernel
      have hl : raw37362step0Labels = raw37362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37362 raw37362Labels permutation434 hz
    mixedMoment B raw37362step0 raw37362step0Labels = mixedMoment B raw37362step1 raw37362step1Labels := by
      have hz : ∀ j, raw37362step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37362step1 = (fun i j => raw37362step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37362step1 raw37362step0; decide +kernel
      have hl : raw37362step1Labels = raw37362step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37362step0 raw37362step0Labels permutation80 hz
    mixedMoment B raw37362step1 raw37362step1Labels = mixedMoment B raw37362step2 raw37362step2Labels := by
      have ha : raw37362step2 = (fun i j => raw37362step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37362step2 raw37362step1; decide +kernel
      have hl : raw37362step2Labels = raw37362step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37362step1 raw37362step1Labels permutation10 permutation4
    mixedMoment B raw37362step2 raw37362step2Labels = mixedMoment B raw37362step3 raw37362step3Labels := by
      have ha : raw37362step3 = -raw37362step2 := by apply Matrix.ext; change ∀ i j, raw37362step3 i j = -(raw37362step2 i j); unfold raw37362step3 raw37362step2; decide +kernel
      have hl : raw37362step3Labels = raw37362step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node665 node665Labels := by rfl

def raw37363 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37363step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw37363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37363step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw37363step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37363 raw37363Labels = mixedMoment B node665 node665Labels := by
  calc
    mixedMoment B raw37363 raw37363Labels = mixedMoment B raw37363step0 raw37363step0Labels := by
      have hz : ∀ j, raw37363 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37363step0 = (fun i j => raw37363 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37363step0 raw37363; decide +kernel
      have hl : raw37363step0Labels = raw37363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37363 raw37363Labels permutation434 hz
    mixedMoment B raw37363step0 raw37363step0Labels = mixedMoment B raw37363step1 raw37363step1Labels := by
      have hz : ∀ j, raw37363step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37363step1 = (fun i j => raw37363step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37363step1 raw37363step0; decide +kernel
      have hl : raw37363step1Labels = raw37363step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37363step0 raw37363step0Labels permutation56 hz
    mixedMoment B raw37363step1 raw37363step1Labels = mixedMoment B raw37363step2 raw37363step2Labels := by
      have ha : raw37363step2 = (fun i j => raw37363step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37363step2 raw37363step1; decide +kernel
      have hl : raw37363step2Labels = raw37363step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37363step1 raw37363step1Labels permutation10 permutation4
    mixedMoment B raw37363step2 raw37363step2Labels = mixedMoment B raw37363step3 raw37363step3Labels := by
      have ha : raw37363step3 = -raw37363step2 := by apply Matrix.ext; change ∀ i j, raw37363step3 i j = -(raw37363step2 i j); unfold raw37363step3 raw37363step2; decide +kernel
      have hl : raw37363step3Labels = raw37363step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node665 node665Labels := by rfl

def raw37364 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37364step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw37364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37364step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw37364step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37364 raw37364Labels = mixedMoment B node665 node665Labels := by
  calc
    mixedMoment B raw37364 raw37364Labels = mixedMoment B raw37364step0 raw37364step0Labels := by
      have hz : ∀ j, raw37364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37364step0 = (fun i j => raw37364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37364step0 raw37364; decide +kernel
      have hl : raw37364step0Labels = raw37364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37364 raw37364Labels permutation346 hz
    mixedMoment B raw37364step0 raw37364step0Labels = mixedMoment B raw37364step1 raw37364step1Labels := by
      have hz : ∀ j, raw37364step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37364step1 = (fun i j => raw37364step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37364step1 raw37364step0; decide +kernel
      have hl : raw37364step1Labels = raw37364step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37364step0 raw37364step0Labels permutation56 hz
    mixedMoment B raw37364step1 raw37364step1Labels = mixedMoment B raw37364step2 raw37364step2Labels := by
      have ha : raw37364step2 = (fun i j => raw37364step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37364step2 raw37364step1; decide +kernel
      have hl : raw37364step2Labels = raw37364step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37364step1 raw37364step1Labels permutation10 permutation4
    mixedMoment B raw37364step2 raw37364step2Labels = mixedMoment B raw37364step3 raw37364step3Labels := by
      have ha : raw37364step3 = -raw37364step2 := by apply Matrix.ext; change ∀ i j, raw37364step3 i j = -(raw37364step2 i j); unfold raw37364step3 raw37364step2; decide +kernel
      have hl : raw37364step3Labels = raw37364step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node665 node665Labels := by rfl

def raw37365 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37365step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![-1, 0, 1], ![0, -4, 4]]
def raw37365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37365step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-4, 0, 4]]
def raw37365step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37365step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![4, 0, -4]]
def raw37365step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37365 raw37365Labels = mixedMoment B node673 node673Labels := by
  calc
    mixedMoment B raw37365 raw37365Labels = mixedMoment B raw37365step0 raw37365step0Labels := by
      have hz : ∀ j, raw37365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37365step0 = (fun i j => raw37365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37365step0 raw37365; decide +kernel
      have hl : raw37365step0Labels = raw37365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37365 raw37365Labels permutation434 hz
    mixedMoment B raw37365step0 raw37365step0Labels = mixedMoment B raw37365step1 raw37365step1Labels := by
      have hz : ∀ j, raw37365step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37365step1 = (fun i j => raw37365step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37365step1 raw37365step0; decide +kernel
      have hl : raw37365step1Labels = raw37365step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37365step0 raw37365step0Labels permutation80 hz
    mixedMoment B raw37365step1 raw37365step1Labels = mixedMoment B raw37365step2 raw37365step2Labels := by
      have hz : ∀ j, raw37365step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37365step2 = (fun i j => raw37365step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37365step2 raw37365step1; decide +kernel
      have hl : raw37365step2Labels = raw37365step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37365step1 raw37365step1Labels permutation14 hz
    mixedMoment B raw37365step2 raw37365step2Labels = mixedMoment B raw37365step3 raw37365step3Labels := by
      have ha : raw37365step3 = (fun i j => raw37365step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37365step3 raw37365step2; decide +kernel
      have hl : raw37365step3Labels = raw37365step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37365step2 raw37365step2Labels permutation2 permutation4
    mixedMoment B raw37365step3 raw37365step3Labels = mixedMoment B raw37365step4 raw37365step4Labels := by
      have ha : raw37365step4 = -raw37365step3 := by apply Matrix.ext; change ∀ i j, raw37365step4 i j = -(raw37365step3 i j); unfold raw37365step4 raw37365step3; decide +kernel
      have hl : raw37365step4Labels = raw37365step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node673 node673Labels := by rfl

def raw37366 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw37366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37366 raw37366Labels = mixedMoment B node765 node765Labels := by
  calc
    mixedMoment B raw37366 raw37366Labels = mixedMoment B raw37366step0 raw37366step0Labels := by
      have hz : ∀ j, raw37366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37366step0 = (fun i j => raw37366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37366step0 raw37366; decide +kernel
      have hl : raw37366step0Labels = raw37366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37366 raw37366Labels permutation434 hz
    mixedMoment B raw37366step0 raw37366step0Labels = mixedMoment B raw37366step1 raw37366step1Labels := by
      have hz : ∀ j, raw37366step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37366step1 = (fun i j => raw37366step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37366step1 raw37366step0; decide +kernel
      have hl : raw37366step1Labels = raw37366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37366step0 raw37366step0Labels permutation80 hz
    mixedMoment B raw37366step1 raw37366step1Labels = mixedMoment B raw37366step2 raw37366step2Labels := by
      have ha : raw37366step2 = (fun i j => raw37366step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37366step2 raw37366step1; decide +kernel
      have hl : raw37366step2Labels = raw37366step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37366step1 raw37366step1Labels permutation31 permutation4
    _ = mixedMoment B node765 node765Labels := by rfl

def raw37367 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37367step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw37367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37367 raw37367Labels = mixedMoment B node765 node765Labels := by
  calc
    mixedMoment B raw37367 raw37367Labels = mixedMoment B raw37367step0 raw37367step0Labels := by
      have hz : ∀ j, raw37367 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37367step0 = (fun i j => raw37367 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37367step0 raw37367; decide +kernel
      have hl : raw37367step0Labels = raw37367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37367 raw37367Labels permutation434 hz
    mixedMoment B raw37367step0 raw37367step0Labels = mixedMoment B raw37367step1 raw37367step1Labels := by
      have hz : ∀ j, raw37367step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37367step1 = (fun i j => raw37367step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37367step1 raw37367step0; decide +kernel
      have hl : raw37367step1Labels = raw37367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37367step0 raw37367step0Labels permutation56 hz
    mixedMoment B raw37367step1 raw37367step1Labels = mixedMoment B raw37367step2 raw37367step2Labels := by
      have ha : raw37367step2 = (fun i j => raw37367step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37367step2 raw37367step1; decide +kernel
      have hl : raw37367step2Labels = raw37367step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37367step1 raw37367step1Labels permutation31 permutation4
    _ = mixedMoment B node765 node765Labels := by rfl

def raw37368 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37368step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw37368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37368 raw37368Labels = mixedMoment B node765 node765Labels := by
  calc
    mixedMoment B raw37368 raw37368Labels = mixedMoment B raw37368step0 raw37368step0Labels := by
      have hz : ∀ j, raw37368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37368step0 = (fun i j => raw37368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37368step0 raw37368; decide +kernel
      have hl : raw37368step0Labels = raw37368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37368 raw37368Labels permutation346 hz
    mixedMoment B raw37368step0 raw37368step0Labels = mixedMoment B raw37368step1 raw37368step1Labels := by
      have hz : ∀ j, raw37368step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37368step1 = (fun i j => raw37368step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37368step1 raw37368step0; decide +kernel
      have hl : raw37368step1Labels = raw37368step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37368step0 raw37368step0Labels permutation56 hz
    mixedMoment B raw37368step1 raw37368step1Labels = mixedMoment B raw37368step2 raw37368step2Labels := by
      have ha : raw37368step2 = (fun i j => raw37368step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37368step2 raw37368step1; decide +kernel
      have hl : raw37368step2Labels = raw37368step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37368step1 raw37368step1Labels permutation31 permutation4
    _ = mixedMoment B node765 node765Labels := by rfl

def raw37369 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -4, 4]]
def raw37369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -4, 4]]
def raw37369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37369step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-2, 1, 1], ![0, -4, 4]]
def raw37369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37369step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![-2, 1, 1], ![0, -4, 4]]
def raw37369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37369step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def raw37369step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37369 raw37369Labels = mixedMoment B node845 node845Labels := by
  calc
    mixedMoment B raw37369 raw37369Labels = mixedMoment B raw37369step0 raw37369step0Labels := by
      have hz : ∀ j, raw37369 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37369step0 = (fun i j => raw37369 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37369step0 raw37369; decide +kernel
      have hl : raw37369step0Labels = raw37369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37369 raw37369Labels permutation434 hz
    mixedMoment B raw37369step0 raw37369step0Labels = mixedMoment B raw37369step1 raw37369step1Labels := by
      have hz : ∀ j, raw37369step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37369step1 = (fun i j => raw37369step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37369step1 raw37369step0; decide +kernel
      have hl : raw37369step1Labels = raw37369step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37369step0 raw37369step0Labels permutation80 hz
    mixedMoment B raw37369step1 raw37369step1Labels = mixedMoment B raw37369step2 raw37369step2Labels := by
      have hz : ∀ j, raw37369step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37369step2 = (fun i j => raw37369step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37369step2 raw37369step1; decide +kernel
      have hl : raw37369step2Labels = raw37369step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37369step1 raw37369step1Labels permutation14 hz
    mixedMoment B raw37369step2 raw37369step2Labels = mixedMoment B raw37369step3 raw37369step3Labels := by
      have ha : raw37369step3 = (fun i j => raw37369step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37369step3 raw37369step2; decide +kernel
      have hl : raw37369step3Labels = raw37369step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37369step2 raw37369step2Labels permutation7 permutation4
    _ = mixedMoment B node845 node845Labels := by rfl

def raw37370 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37370step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw37370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37370step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw37370step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37370 raw37370Labels = mixedMoment B node1527 node1527Labels := by
  calc
    mixedMoment B raw37370 raw37370Labels = mixedMoment B raw37370step0 raw37370step0Labels := by
      have hz : ∀ j, raw37370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37370step0 = (fun i j => raw37370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37370step0 raw37370; decide +kernel
      have hl : raw37370step0Labels = raw37370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37370 raw37370Labels permutation434 hz
    mixedMoment B raw37370step0 raw37370step0Labels = mixedMoment B raw37370step1 raw37370step1Labels := by
      have hz : ∀ j, raw37370step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37370step1 = (fun i j => raw37370step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37370step1 raw37370step0; decide +kernel
      have hl : raw37370step1Labels = raw37370step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37370step0 raw37370step0Labels permutation80 hz
    mixedMoment B raw37370step1 raw37370step1Labels = mixedMoment B raw37370step2 raw37370step2Labels := by
      have hz : ∀ j, raw37370step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37370step2 = (fun i j => raw37370step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37370step2 raw37370step1; decide +kernel
      have hl : raw37370step2Labels = raw37370step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37370step1 raw37370step1Labels permutation14 hz
    mixedMoment B raw37370step2 raw37370step2Labels = mixedMoment B raw37370step3 raw37370step3Labels := by
      have ha : raw37370step3 = -raw37370step2 := by apply Matrix.ext; change ∀ i j, raw37370step3 i j = -(raw37370step2 i j); unfold raw37370step3 raw37370step2; decide +kernel
      have hl : raw37370step3Labels = raw37370step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1527 node1527Labels := by rfl

def raw37371 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw37371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37371step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37371step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37371 raw37371Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw37371 raw37371Labels = mixedMoment B raw37371step0 raw37371step0Labels := by
      have hz : ∀ j, raw37371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37371step0 = (fun i j => raw37371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37371step0 raw37371; decide +kernel
      have hl : raw37371step0Labels = raw37371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37371 raw37371Labels permutation434 hz
    mixedMoment B raw37371step0 raw37371step0Labels = mixedMoment B raw37371step1 raw37371step1Labels := by
      have hz : ∀ j, raw37371step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37371step1 = (fun i j => raw37371step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37371step1 raw37371step0; decide +kernel
      have hl : raw37371step1Labels = raw37371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37371step0 raw37371step0Labels permutation80 hz
    mixedMoment B raw37371step1 raw37371step1Labels = mixedMoment B raw37371step2 raw37371step2Labels := by
      have ha : raw37371step2 = (fun i j => raw37371step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37371step2 raw37371step1; decide +kernel
      have hl : raw37371step2Labels = raw37371step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37371step1 raw37371step1Labels permutation12 permutation4
    mixedMoment B raw37371step2 raw37371step2Labels = mixedMoment B raw37371step3 raw37371step3Labels := by
      have ha : raw37371step3 = -raw37371step2 := by apply Matrix.ext; change ∀ i j, raw37371step3 i j = -(raw37371step2 i j); unfold raw37371step3 raw37371step2; decide +kernel
      have hl : raw37371step3Labels = raw37371step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1529 node1529Labels := by rfl

def raw37372 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37372step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37372step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw37372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37372step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37372step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37372 raw37372Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw37372 raw37372Labels = mixedMoment B raw37372step0 raw37372step0Labels := by
      have hz : ∀ j, raw37372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37372step0 = (fun i j => raw37372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37372step0 raw37372; decide +kernel
      have hl : raw37372step0Labels = raw37372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37372 raw37372Labels permutation434 hz
    mixedMoment B raw37372step0 raw37372step0Labels = mixedMoment B raw37372step1 raw37372step1Labels := by
      have hz : ∀ j, raw37372step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37372step1 = (fun i j => raw37372step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37372step1 raw37372step0; decide +kernel
      have hl : raw37372step1Labels = raw37372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37372step0 raw37372step0Labels permutation56 hz
    mixedMoment B raw37372step1 raw37372step1Labels = mixedMoment B raw37372step2 raw37372step2Labels := by
      have ha : raw37372step2 = (fun i j => raw37372step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37372step2 raw37372step1; decide +kernel
      have hl : raw37372step2Labels = raw37372step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37372step1 raw37372step1Labels permutation12 permutation4
    mixedMoment B raw37372step2 raw37372step2Labels = mixedMoment B raw37372step3 raw37372step3Labels := by
      have ha : raw37372step3 = -raw37372step2 := by apply Matrix.ext; change ∀ i j, raw37372step3 i j = -(raw37372step2 i j); unfold raw37372step3 raw37372step2; decide +kernel
      have hl : raw37372step3Labels = raw37372step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1529 node1529Labels := by rfl

def raw37373 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37373step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw37373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37373step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37373step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37373 raw37373Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw37373 raw37373Labels = mixedMoment B raw37373step0 raw37373step0Labels := by
      have hz : ∀ j, raw37373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37373step0 = (fun i j => raw37373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37373step0 raw37373; decide +kernel
      have hl : raw37373step0Labels = raw37373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37373 raw37373Labels permutation346 hz
    mixedMoment B raw37373step0 raw37373step0Labels = mixedMoment B raw37373step1 raw37373step1Labels := by
      have hz : ∀ j, raw37373step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37373step1 = (fun i j => raw37373step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37373step1 raw37373step0; decide +kernel
      have hl : raw37373step1Labels = raw37373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37373step0 raw37373step0Labels permutation56 hz
    mixedMoment B raw37373step1 raw37373step1Labels = mixedMoment B raw37373step2 raw37373step2Labels := by
      have ha : raw37373step2 = (fun i j => raw37373step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37373step2 raw37373step1; decide +kernel
      have hl : raw37373step2Labels = raw37373step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37373step1 raw37373step1Labels permutation12 permutation4
    mixedMoment B raw37373step2 raw37373step2Labels = mixedMoment B raw37373step3 raw37373step3Labels := by
      have ha : raw37373step3 = -raw37373step2 := by apply Matrix.ext; change ∀ i j, raw37373step3 i j = -(raw37373step2 i j); unfold raw37373step3 raw37373step2; decide +kernel
      have hl : raw37373step3Labels = raw37373step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1529 node1529Labels := by rfl

def raw37374 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37374step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -3, 2], ![-3, 0, 3]]
def raw37374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37374step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-3, 1, 2]]
def raw37374step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37374step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw37374step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37374 raw37374Labels = mixedMoment B node1531 node1531Labels := by
  calc
    mixedMoment B raw37374 raw37374Labels = mixedMoment B raw37374step0 raw37374step0Labels := by
      have hz : ∀ j, raw37374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37374step0 = (fun i j => raw37374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37374step0 raw37374; decide +kernel
      have hl : raw37374step0Labels = raw37374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37374 raw37374Labels permutation434 hz
    mixedMoment B raw37374step0 raw37374step0Labels = mixedMoment B raw37374step1 raw37374step1Labels := by
      have hz : ∀ j, raw37374step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37374step1 = (fun i j => raw37374step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37374step1 raw37374step0; decide +kernel
      have hl : raw37374step1Labels = raw37374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37374step0 raw37374step0Labels permutation80 hz
    mixedMoment B raw37374step1 raw37374step1Labels = mixedMoment B raw37374step2 raw37374step2Labels := by
      have hz : ∀ j, raw37374step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37374step2 = (fun i j => raw37374step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37374step2 raw37374step1; decide +kernel
      have hl : raw37374step2Labels = raw37374step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37374step1 raw37374step1Labels permutation14 hz
    mixedMoment B raw37374step2 raw37374step2Labels = mixedMoment B raw37374step3 raw37374step3Labels := by
      have ha : raw37374step3 = (fun i j => raw37374step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37374step3 raw37374step2; decide +kernel
      have hl : raw37374step3Labels = raw37374step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37374step2 raw37374step2Labels permutation3 permutation4
    mixedMoment B raw37374step3 raw37374step3Labels = mixedMoment B raw37374step4 raw37374step4Labels := by
      have ha : raw37374step4 = -raw37374step3 := by apply Matrix.ext; change ∀ i j, raw37374step4 i j = -(raw37374step3 i j); unfold raw37374step4 raw37374step3; decide +kernel
      have hl : raw37374step4Labels = raw37374step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1531 node1531Labels := by rfl

def raw37375 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37375step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![0, -2, 2], ![-2, -1, 3]]
def raw37375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37375step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -2, 3], ![-2, 0, 2]]
def raw37375step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37375step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw37375step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37375 raw37375Labels = mixedMoment B node1539 node1539Labels := by
  calc
    mixedMoment B raw37375 raw37375Labels = mixedMoment B raw37375step0 raw37375step0Labels := by
      have hz : ∀ j, raw37375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37375step0 = (fun i j => raw37375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37375step0 raw37375; decide +kernel
      have hl : raw37375step0Labels = raw37375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37375 raw37375Labels permutation434 hz
    mixedMoment B raw37375step0 raw37375step0Labels = mixedMoment B raw37375step1 raw37375step1Labels := by
      have hz : ∀ j, raw37375step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37375step1 = (fun i j => raw37375step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37375step1 raw37375step0; decide +kernel
      have hl : raw37375step1Labels = raw37375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37375step0 raw37375step0Labels permutation80 hz
    mixedMoment B raw37375step1 raw37375step1Labels = mixedMoment B raw37375step2 raw37375step2Labels := by
      have hz : ∀ j, raw37375step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37375step2 = (fun i j => raw37375step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37375step2 raw37375step1; decide +kernel
      have hl : raw37375step2Labels = raw37375step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37375step1 raw37375step1Labels permutation14 hz
    mixedMoment B raw37375step2 raw37375step2Labels = mixedMoment B raw37375step3 raw37375step3Labels := by
      have ha : raw37375step3 = (fun i j => raw37375step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37375step3 raw37375step2; decide +kernel
      have hl : raw37375step3Labels = raw37375step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37375step2 raw37375step2Labels permutation3 permutation4
    mixedMoment B raw37375step3 raw37375step3Labels = mixedMoment B raw37375step4 raw37375step4Labels := by
      have ha : raw37375step4 = -raw37375step3 := by apply Matrix.ext; change ∀ i j, raw37375step4 i j = -(raw37375step3 i j); unfold raw37375step4 raw37375step3; decide +kernel
      have hl : raw37375step4Labels = raw37375step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1539 node1539Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
