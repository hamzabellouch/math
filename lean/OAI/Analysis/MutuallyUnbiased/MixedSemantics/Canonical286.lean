import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36608 raw36608Labels = mixedMoment B node4951 node4951Labels := by
  calc
    mixedMoment B raw36608 raw36608Labels = mixedMoment B raw36608step0 raw36608step0Labels := by
      have hz : ∀ j, raw36608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36608step0 = (fun i j => raw36608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36608step0 raw36608; decide +kernel
      have hl : raw36608step0Labels = raw36608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36608 raw36608Labels permutation346 hz
    mixedMoment B raw36608step0 raw36608step0Labels = mixedMoment B raw36608step1 raw36608step1Labels := by
      have ha : raw36608step1 = (fun i j => raw36608step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36608step1 raw36608step0; decide +kernel
      have hl : raw36608step1Labels = raw36608step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36608step0 raw36608step0Labels permutation57 permutation2
    _ = mixedMoment B node4951 node4951Labels := by rfl

def raw36609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36609 raw36609Labels = mixedMoment B node5338 node5338Labels := by
  calc
    mixedMoment B raw36609 raw36609Labels = mixedMoment B raw36609step0 raw36609step0Labels := by
      have ha : raw36609step0 = (fun i j => raw36609 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36609step0 raw36609; decide +kernel
      have hl : raw36609step0Labels = raw36609Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36609 raw36609Labels permutation266 permutation2
    _ = mixedMoment B node5338 node5338Labels := by rfl

def raw36610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36610 raw36610Labels = mixedMoment B node5361 node5361Labels := by
  calc
    mixedMoment B raw36610 raw36610Labels = mixedMoment B raw36610step0 raw36610step0Labels := by
      have hz : ∀ j, raw36610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36610step0 = (fun i j => raw36610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36610step0 raw36610; decide +kernel
      have hl : raw36610step0Labels = raw36610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36610 raw36610Labels permutation346 hz
    mixedMoment B raw36610step0 raw36610step0Labels = mixedMoment B raw36610step1 raw36610step1Labels := by
      have ha : raw36610step1 = (fun i j => raw36610step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36610step1 raw36610step0; decide +kernel
      have hl : raw36610step1Labels = raw36610step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36610step0 raw36610step0Labels permutation57 permutation2
    _ = mixedMoment B node5361 node5361Labels := by rfl

def raw36611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw36611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw36611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36611 raw36611Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw36611 raw36611Labels = mixedMoment B raw36611step0 raw36611step0Labels := by
      have hz : ∀ j, raw36611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36611step0 = (fun i j => raw36611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36611step0 raw36611; decide +kernel
      have hl : raw36611step0Labels = raw36611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36611 raw36611Labels permutation346 hz
    mixedMoment B raw36611step0 raw36611step0Labels = mixedMoment B raw36611step1 raw36611step1Labels := by
      have ha : raw36611step1 = (fun i j => raw36611step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36611step1 raw36611step0; decide +kernel
      have hl : raw36611step1Labels = raw36611step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36611step0 raw36611step0Labels permutation60 permutation2
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw36612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw36612step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw36612step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36612step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw36612step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36612 raw36612Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw36612 raw36612Labels = mixedMoment B raw36612step0 raw36612step0Labels := by
      have hz : ∀ j, raw36612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36612step0 = (fun i j => raw36612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36612step0 raw36612; decide +kernel
      have hl : raw36612step0Labels = raw36612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36612 raw36612Labels permutation346 hz
    mixedMoment B raw36612step0 raw36612step0Labels = mixedMoment B raw36612step1 raw36612step1Labels := by
      have ha : raw36612step1 = (fun i j => raw36612step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36612step1 raw36612step0; decide +kernel
      have hl : raw36612step1Labels = raw36612step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36612step0 raw36612step0Labels permutation151 permutation3
    mixedMoment B raw36612step1 raw36612step1Labels = mixedMoment B raw36612step2 raw36612step2Labels := by
      have ha : raw36612step2 = -raw36612step1 := by apply Matrix.ext; change ∀ i j, raw36612step2 i j = -(raw36612step1 i j); unfold raw36612step2 raw36612step1; decide +kernel
      have hl : raw36612step2Labels = raw36612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36612step2 raw36612step2Labels = mixedMoment B raw36612step3 raw36612step3Labels := by
      have ha : raw36612step3 = raw36612step2 := by apply Matrix.ext; unfold raw36612step3 raw36612step2; decide +kernel
      have hl : raw36612step2Labels = labelEmbedding6 ∘ raw36612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36612step2 raw36612step2Labels raw36612step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4776 node4776Labels := by rfl

def raw36613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw36613step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw36613step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36613step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw36613step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36613 raw36613Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw36613 raw36613Labels = mixedMoment B raw36613step0 raw36613step0Labels := by
      have hz : ∀ j, raw36613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36613step0 = (fun i j => raw36613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36613step0 raw36613; decide +kernel
      have hl : raw36613step0Labels = raw36613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36613 raw36613Labels permutation346 hz
    mixedMoment B raw36613step0 raw36613step0Labels = mixedMoment B raw36613step1 raw36613step1Labels := by
      have ha : raw36613step1 = (fun i j => raw36613step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36613step1 raw36613step0; decide +kernel
      have hl : raw36613step1Labels = raw36613step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36613step0 raw36613step0Labels permutation150 permutation3
    mixedMoment B raw36613step1 raw36613step1Labels = mixedMoment B raw36613step2 raw36613step2Labels := by
      have ha : raw36613step2 = -raw36613step1 := by apply Matrix.ext; change ∀ i j, raw36613step2 i j = -(raw36613step1 i j); unfold raw36613step2 raw36613step1; decide +kernel
      have hl : raw36613step2Labels = raw36613step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36613step2 raw36613step2Labels = mixedMoment B raw36613step3 raw36613step3Labels := by
      have ha : raw36613step3 = raw36613step2 := by apply Matrix.ext; unfold raw36613step3 raw36613step2; decide +kernel
      have hl : raw36613step2Labels = labelEmbedding6 ∘ raw36613step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36613step2 raw36613step2Labels raw36613step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4777 node4777Labels := by rfl

def raw36614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36614step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36614step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36614 raw36614Labels = mixedMoment B node4775 node4775Labels := by
  calc
    mixedMoment B raw36614 raw36614Labels = mixedMoment B raw36614step0 raw36614step0Labels := by
      have ha : raw36614step0 = (fun i j => raw36614 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36614step0 raw36614; decide +kernel
      have hl : raw36614step0Labels = raw36614Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36614 raw36614Labels permutation688 permutation3
    mixedMoment B raw36614step0 raw36614step0Labels = mixedMoment B raw36614step1 raw36614step1Labels := by
      have ha : raw36614step1 = -raw36614step0 := by apply Matrix.ext; change ∀ i j, raw36614step1 i j = -(raw36614step0 i j); unfold raw36614step1 raw36614step0; decide +kernel
      have hl : raw36614step1Labels = raw36614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36614step1 raw36614step1Labels = mixedMoment B raw36614step2 raw36614step2Labels := by
      have ha : raw36614step2 = raw36614step1 := by apply Matrix.ext; unfold raw36614step2 raw36614step1; decide +kernel
      have hl : raw36614step1Labels = labelEmbedding6 ∘ raw36614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36614step1 raw36614step1Labels raw36614step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4775 node4775Labels := by rfl

def raw36615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36615step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36615step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36615step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36615step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36615 raw36615Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw36615 raw36615Labels = mixedMoment B raw36615step0 raw36615step0Labels := by
      have hz : ∀ j, raw36615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36615step0 = (fun i j => raw36615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36615step0 raw36615; decide +kernel
      have hl : raw36615step0Labels = raw36615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36615 raw36615Labels permutation346 hz
    mixedMoment B raw36615step0 raw36615step0Labels = mixedMoment B raw36615step1 raw36615step1Labels := by
      have ha : raw36615step1 = (fun i j => raw36615step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36615step1 raw36615step0; decide +kernel
      have hl : raw36615step1Labels = raw36615step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36615step0 raw36615step0Labels permutation151 permutation3
    mixedMoment B raw36615step1 raw36615step1Labels = mixedMoment B raw36615step2 raw36615step2Labels := by
      have ha : raw36615step2 = -raw36615step1 := by apply Matrix.ext; change ∀ i j, raw36615step2 i j = -(raw36615step1 i j); unfold raw36615step2 raw36615step1; decide +kernel
      have hl : raw36615step2Labels = raw36615step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36615step2 raw36615step2Labels = mixedMoment B raw36615step3 raw36615step3Labels := by
      have ha : raw36615step3 = raw36615step2 := by apply Matrix.ext; unfold raw36615step3 raw36615step2; decide +kernel
      have hl : raw36615step2Labels = labelEmbedding6 ∘ raw36615step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36615step2 raw36615step2Labels raw36615step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw36616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw36616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw36616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36616step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36616step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36616step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36616step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36616 raw36616Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw36616 raw36616Labels = mixedMoment B raw36616step0 raw36616step0Labels := by
      have hz : ∀ j, raw36616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36616step0 = (fun i j => raw36616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36616step0 raw36616; decide +kernel
      have hl : raw36616step0Labels = raw36616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36616 raw36616Labels permutation346 hz
    mixedMoment B raw36616step0 raw36616step0Labels = mixedMoment B raw36616step1 raw36616step1Labels := by
      have ha : raw36616step1 = (fun i j => raw36616step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36616step1 raw36616step0; decide +kernel
      have hl : raw36616step1Labels = raw36616step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36616step0 raw36616step0Labels permutation145 permutation3
    mixedMoment B raw36616step1 raw36616step1Labels = mixedMoment B raw36616step2 raw36616step2Labels := by
      have ha : raw36616step2 = -raw36616step1 := by apply Matrix.ext; change ∀ i j, raw36616step2 i j = -(raw36616step1 i j); unfold raw36616step2 raw36616step1; decide +kernel
      have hl : raw36616step2Labels = raw36616step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36616step2 raw36616step2Labels = mixedMoment B raw36616step3 raw36616step3Labels := by
      have ha : raw36616step3 = raw36616step2 := by apply Matrix.ext; unfold raw36616step3 raw36616step2; decide +kernel
      have hl : raw36616step2Labels = labelEmbedding6 ∘ raw36616step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36616step2 raw36616step2Labels raw36616step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw36617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36617step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36617step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36617 raw36617Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw36617 raw36617Labels = mixedMoment B raw36617step0 raw36617step0Labels := by
      have hz : ∀ j, raw36617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36617step0 = (fun i j => raw36617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36617step0 raw36617; decide +kernel
      have hl : raw36617step0Labels = raw36617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36617 raw36617Labels permutation346 hz
    mixedMoment B raw36617step0 raw36617step0Labels = mixedMoment B raw36617step1 raw36617step1Labels := by
      have ha : raw36617step1 = (fun i j => raw36617step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36617step1 raw36617step0; decide +kernel
      have hl : raw36617step1Labels = raw36617step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36617step0 raw36617step0Labels permutation61 permutation7
    mixedMoment B raw36617step1 raw36617step1Labels = mixedMoment B raw36617step2 raw36617step2Labels := by
      have ha : raw36617step2 = -raw36617step1 := by apply Matrix.ext; change ∀ i j, raw36617step2 i j = -(raw36617step1 i j); unfold raw36617step2 raw36617step1; decide +kernel
      have hl : raw36617step2Labels = raw36617step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36617step2 raw36617step2Labels = mixedMoment B raw36617step3 raw36617step3Labels := by
      have ha : raw36617step3 = raw36617step2 := by apply Matrix.ext; unfold raw36617step3 raw36617step2; decide +kernel
      have hl : raw36617step2Labels = labelEmbedding1 ∘ raw36617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36617step2 raw36617step2Labels raw36617step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

def raw36618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36618 raw36618Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw36618 raw36618Labels = mixedMoment B raw36618step0 raw36618step0Labels := by
      have ha : raw36618step0 = (fun i j => raw36618 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36618step0 raw36618; decide +kernel
      have hl : raw36618step0Labels = raw36618Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36618 raw36618Labels permutation270 permutation7
    mixedMoment B raw36618step0 raw36618step0Labels = mixedMoment B raw36618step1 raw36618step1Labels := by
      have ha : raw36618step1 = -raw36618step0 := by apply Matrix.ext; change ∀ i j, raw36618step1 i j = -(raw36618step0 i j); unfold raw36618step1 raw36618step0; decide +kernel
      have hl : raw36618step1Labels = raw36618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36618step1 raw36618step1Labels = mixedMoment B raw36618step2 raw36618step2Labels := by
      have ha : raw36618step2 = raw36618step1 := by apply Matrix.ext; unfold raw36618step2 raw36618step1; decide +kernel
      have hl : raw36618step1Labels = labelEmbedding1 ∘ raw36618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36618step1 raw36618step1Labels raw36618step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw36619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36619step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw36619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36619step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36619step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36619step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36619 raw36619Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw36619 raw36619Labels = mixedMoment B raw36619step0 raw36619step0Labels := by
      have hz : ∀ j, raw36619 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36619step0 = (fun i j => raw36619 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36619step0 raw36619; decide +kernel
      have hl : raw36619step0Labels = raw36619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36619 raw36619Labels permutation346 hz
    mixedMoment B raw36619step0 raw36619step0Labels = mixedMoment B raw36619step1 raw36619step1Labels := by
      have ha : raw36619step1 = (fun i j => raw36619step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36619step1 raw36619step0; decide +kernel
      have hl : raw36619step1Labels = raw36619step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36619step0 raw36619step0Labels permutation61 permutation7
    mixedMoment B raw36619step1 raw36619step1Labels = mixedMoment B raw36619step2 raw36619step2Labels := by
      have ha : raw36619step2 = -raw36619step1 := by apply Matrix.ext; change ∀ i j, raw36619step2 i j = -(raw36619step1 i j); unfold raw36619step2 raw36619step1; decide +kernel
      have hl : raw36619step2Labels = raw36619step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36619step2 raw36619step2Labels = mixedMoment B raw36619step3 raw36619step3Labels := by
      have ha : raw36619step3 = raw36619step2 := by apply Matrix.ext; unfold raw36619step3 raw36619step2; decide +kernel
      have hl : raw36619step2Labels = labelEmbedding1 ∘ raw36619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36619step2 raw36619step2Labels raw36619step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw36620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw36620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36620step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36620step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36620step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36620 raw36620Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw36620 raw36620Labels = mixedMoment B raw36620step0 raw36620step0Labels := by
      have hz : ∀ j, raw36620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36620step0 = (fun i j => raw36620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36620step0 raw36620; decide +kernel
      have hl : raw36620step0Labels = raw36620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36620 raw36620Labels permutation346 hz
    mixedMoment B raw36620step0 raw36620step0Labels = mixedMoment B raw36620step1 raw36620step1Labels := by
      have ha : raw36620step1 = (fun i j => raw36620step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36620step1 raw36620step0; decide +kernel
      have hl : raw36620step1Labels = raw36620step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36620step0 raw36620step0Labels permutation61 permutation7
    mixedMoment B raw36620step1 raw36620step1Labels = mixedMoment B raw36620step2 raw36620step2Labels := by
      have ha : raw36620step2 = -raw36620step1 := by apply Matrix.ext; change ∀ i j, raw36620step2 i j = -(raw36620step1 i j); unfold raw36620step2 raw36620step1; decide +kernel
      have hl : raw36620step2Labels = raw36620step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36620step2 raw36620step2Labels = mixedMoment B raw36620step3 raw36620step3Labels := by
      have ha : raw36620step3 = raw36620step2 := by apply Matrix.ext; unfold raw36620step3 raw36620step2; decide +kernel
      have hl : raw36620step2Labels = labelEmbedding1 ∘ raw36620step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36620step2 raw36620step2Labels raw36620step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw36621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36621step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36621step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36621 raw36621Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw36621 raw36621Labels = mixedMoment B raw36621step0 raw36621step0Labels := by
      have hz : ∀ j, raw36621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36621step0 = (fun i j => raw36621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36621step0 raw36621; decide +kernel
      have hl : raw36621step0Labels = raw36621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36621 raw36621Labels permutation346 hz
    mixedMoment B raw36621step0 raw36621step0Labels = mixedMoment B raw36621step1 raw36621step1Labels := by
      have ha : raw36621step1 = (fun i j => raw36621step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36621step1 raw36621step0; decide +kernel
      have hl : raw36621step1Labels = raw36621step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36621step0 raw36621step0Labels permutation61 permutation7
    mixedMoment B raw36621step1 raw36621step1Labels = mixedMoment B raw36621step2 raw36621step2Labels := by
      have ha : raw36621step2 = -raw36621step1 := by apply Matrix.ext; change ∀ i j, raw36621step2 i j = -(raw36621step1 i j); unfold raw36621step2 raw36621step1; decide +kernel
      have hl : raw36621step2Labels = raw36621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36621step2 raw36621step2Labels = mixedMoment B raw36621step3 raw36621step3Labels := by
      have ha : raw36621step3 = raw36621step2 := by apply Matrix.ext; unfold raw36621step3 raw36621step2; decide +kernel
      have hl : raw36621step2Labels = labelEmbedding1 ∘ raw36621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36621step2 raw36621step2Labels raw36621step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw36622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw36622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36622 raw36622Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw36622 raw36622Labels = mixedMoment B raw36622step0 raw36622step0Labels := by
      have hz : ∀ j, raw36622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36622step0 = (fun i j => raw36622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36622step0 raw36622; decide +kernel
      have hl : raw36622step0Labels = raw36622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36622 raw36622Labels permutation346 hz
    mixedMoment B raw36622step0 raw36622step0Labels = mixedMoment B raw36622step1 raw36622step1Labels := by
      have ha : raw36622step1 = (fun i j => raw36622step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36622step1 raw36622step0; decide +kernel
      have hl : raw36622step1Labels = raw36622step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36622step0 raw36622step0Labels permutation40 permutation5
    mixedMoment B raw36622step1 raw36622step1Labels = mixedMoment B raw36622step2 raw36622step2Labels := by
      have ha : raw36622step2 = -raw36622step1 := by apply Matrix.ext; change ∀ i j, raw36622step2 i j = -(raw36622step1 i j); unfold raw36622step2 raw36622step1; decide +kernel
      have hl : raw36622step2Labels = raw36622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36622step2 raw36622step2Labels = mixedMoment B raw36622step3 raw36622step3Labels := by
      have ha : raw36622step3 = raw36622step2 := by apply Matrix.ext; unfold raw36622step3 raw36622step2; decide +kernel
      have hl : raw36622step2Labels = labelEmbedding1 ∘ raw36622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36622step2 raw36622step2Labels raw36622step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw36623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36623 raw36623Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw36623 raw36623Labels = mixedMoment B raw36623step0 raw36623step0Labels := by
      have ha : raw36623step0 = (fun i j => raw36623 (permutation622 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36623step0 raw36623; decide +kernel
      have hl : raw36623step0Labels = raw36623Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36623 raw36623Labels permutation622 permutation5
    mixedMoment B raw36623step0 raw36623step0Labels = mixedMoment B raw36623step1 raw36623step1Labels := by
      have ha : raw36623step1 = raw36623step0 := by apply Matrix.ext; unfold raw36623step1 raw36623step0; decide +kernel
      have hl : raw36623step0Labels = labelEmbedding1 ∘ raw36623step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36623step0 raw36623step0Labels raw36623step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw36624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36624step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw36624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw36624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36624 raw36624Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw36624 raw36624Labels = mixedMoment B raw36624step0 raw36624step0Labels := by
      have hz : ∀ j, raw36624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36624step0 = (fun i j => raw36624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36624step0 raw36624; decide +kernel
      have hl : raw36624step0Labels = raw36624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36624 raw36624Labels permutation346 hz
    mixedMoment B raw36624step0 raw36624step0Labels = mixedMoment B raw36624step1 raw36624step1Labels := by
      have ha : raw36624step1 = (fun i j => raw36624step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36624step1 raw36624step0; decide +kernel
      have hl : raw36624step1Labels = raw36624step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36624step0 raw36624step0Labels permutation138 permutation5
    mixedMoment B raw36624step1 raw36624step1Labels = mixedMoment B raw36624step2 raw36624step2Labels := by
      have ha : raw36624step2 = raw36624step1 := by apply Matrix.ext; unfold raw36624step2 raw36624step1; decide +kernel
      have hl : raw36624step1Labels = labelEmbedding1 ∘ raw36624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36624step1 raw36624step1Labels raw36624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw36625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36625step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw36625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw36625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36625 raw36625Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw36625 raw36625Labels = mixedMoment B raw36625step0 raw36625step0Labels := by
      have hz : ∀ j, raw36625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36625step0 = (fun i j => raw36625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36625step0 raw36625; decide +kernel
      have hl : raw36625step0Labels = raw36625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36625 raw36625Labels permutation346 hz
    mixedMoment B raw36625step0 raw36625step0Labels = mixedMoment B raw36625step1 raw36625step1Labels := by
      have ha : raw36625step1 = (fun i j => raw36625step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36625step1 raw36625step0; decide +kernel
      have hl : raw36625step1Labels = raw36625step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36625step0 raw36625step0Labels permutation137 permutation5
    mixedMoment B raw36625step1 raw36625step1Labels = mixedMoment B raw36625step2 raw36625step2Labels := by
      have ha : raw36625step2 = raw36625step1 := by apply Matrix.ext; unfold raw36625step2 raw36625step1; decide +kernel
      have hl : raw36625step1Labels = labelEmbedding1 ∘ raw36625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36625step1 raw36625step1Labels raw36625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw36626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36626step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36626step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36626 raw36626Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw36626 raw36626Labels = mixedMoment B raw36626step0 raw36626step0Labels := by
      have hz : ∀ j, raw36626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36626step0 = (fun i j => raw36626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36626step0 raw36626; decide +kernel
      have hl : raw36626step0Labels = raw36626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36626 raw36626Labels permutation346 hz
    mixedMoment B raw36626step0 raw36626step0Labels = mixedMoment B raw36626step1 raw36626step1Labels := by
      have ha : raw36626step1 = (fun i j => raw36626step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36626step1 raw36626step0; decide +kernel
      have hl : raw36626step1Labels = raw36626step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36626step0 raw36626step0Labels permutation61 permutation7
    mixedMoment B raw36626step1 raw36626step1Labels = mixedMoment B raw36626step2 raw36626step2Labels := by
      have ha : raw36626step2 = -raw36626step1 := by apply Matrix.ext; change ∀ i j, raw36626step2 i j = -(raw36626step1 i j); unfold raw36626step2 raw36626step1; decide +kernel
      have hl : raw36626step2Labels = raw36626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36626step2 raw36626step2Labels = mixedMoment B raw36626step3 raw36626step3Labels := by
      have ha : raw36626step3 = raw36626step2 := by apply Matrix.ext; unfold raw36626step3 raw36626step2; decide +kernel
      have hl : raw36626step2Labels = labelEmbedding1 ∘ raw36626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36626step2 raw36626step2Labels raw36626step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw36627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36627step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36627step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36627step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36627 raw36627Labels = mixedMoment B node3553 node3553Labels := by
  calc
    mixedMoment B raw36627 raw36627Labels = mixedMoment B raw36627step0 raw36627step0Labels := by
      have ha : raw36627step0 = (fun i j => raw36627 (permutation202 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36627step0 raw36627; decide +kernel
      have hl : raw36627step0Labels = raw36627Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36627 raw36627Labels permutation202 permutation5
    mixedMoment B raw36627step0 raw36627step0Labels = mixedMoment B raw36627step1 raw36627step1Labels := by
      have ha : raw36627step1 = -raw36627step0 := by apply Matrix.ext; change ∀ i j, raw36627step1 i j = -(raw36627step0 i j); unfold raw36627step1 raw36627step0; decide +kernel
      have hl : raw36627step1Labels = raw36627step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36627step1 raw36627step1Labels = mixedMoment B raw36627step2 raw36627step2Labels := by
      have ha : raw36627step2 = raw36627step1 := by apply Matrix.ext; unfold raw36627step2 raw36627step1; decide +kernel
      have hl : raw36627step1Labels = labelEmbedding1 ∘ raw36627step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36627step1 raw36627step1Labels raw36627step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3553 node3553Labels := by rfl

def raw36628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36628 raw36628Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw36628 raw36628Labels = mixedMoment B raw36628step0 raw36628step0Labels := by
      have ha : raw36628step0 = (fun i j => raw36628 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36628step0 raw36628; decide +kernel
      have hl : raw36628step0Labels = raw36628Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36628 raw36628Labels permutation270 permutation7
    mixedMoment B raw36628step0 raw36628step0Labels = mixedMoment B raw36628step1 raw36628step1Labels := by
      have ha : raw36628step1 = -raw36628step0 := by apply Matrix.ext; change ∀ i j, raw36628step1 i j = -(raw36628step0 i j); unfold raw36628step1 raw36628step0; decide +kernel
      have hl : raw36628step1Labels = raw36628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36628step1 raw36628step1Labels = mixedMoment B raw36628step2 raw36628step2Labels := by
      have ha : raw36628step2 = raw36628step1 := by apply Matrix.ext; unfold raw36628step2 raw36628step1; decide +kernel
      have hl : raw36628step1Labels = labelEmbedding1 ∘ raw36628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36628step1 raw36628step1Labels raw36628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

def raw36629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw36629step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36629step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36629 raw36629Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw36629 raw36629Labels = mixedMoment B raw36629step0 raw36629step0Labels := by
      have ha : raw36629step0 = (fun i j => raw36629 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36629step0 raw36629; decide +kernel
      have hl : raw36629step0Labels = raw36629Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36629 raw36629Labels permutation270 permutation7
    mixedMoment B raw36629step0 raw36629step0Labels = mixedMoment B raw36629step1 raw36629step1Labels := by
      have ha : raw36629step1 = -raw36629step0 := by apply Matrix.ext; change ∀ i j, raw36629step1 i j = -(raw36629step0 i j); unfold raw36629step1 raw36629step0; decide +kernel
      have hl : raw36629step1Labels = raw36629step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36629step1 raw36629step1Labels = mixedMoment B raw36629step2 raw36629step2Labels := by
      have ha : raw36629step2 = raw36629step1 := by apply Matrix.ext; unfold raw36629step2 raw36629step1; decide +kernel
      have hl : raw36629step1Labels = labelEmbedding1 ∘ raw36629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36629step1 raw36629step1Labels raw36629step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw36630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw36630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36630step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36630 raw36630Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw36630 raw36630Labels = mixedMoment B raw36630step0 raw36630step0Labels := by
      have ha : raw36630step0 = (fun i j => raw36630 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36630step0 raw36630; decide +kernel
      have hl : raw36630step0Labels = raw36630Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36630 raw36630Labels permutation270 permutation7
    mixedMoment B raw36630step0 raw36630step0Labels = mixedMoment B raw36630step1 raw36630step1Labels := by
      have ha : raw36630step1 = -raw36630step0 := by apply Matrix.ext; change ∀ i j, raw36630step1 i j = -(raw36630step0 i j); unfold raw36630step1 raw36630step0; decide +kernel
      have hl : raw36630step1Labels = raw36630step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36630step1 raw36630step1Labels = mixedMoment B raw36630step2 raw36630step2Labels := by
      have ha : raw36630step2 = raw36630step1 := by apply Matrix.ext; unfold raw36630step2 raw36630step1; decide +kernel
      have hl : raw36630step1Labels = labelEmbedding1 ∘ raw36630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36630step1 raw36630step1Labels raw36630step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw36631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36631step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36631 raw36631Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw36631 raw36631Labels = mixedMoment B raw36631step0 raw36631step0Labels := by
      have ha : raw36631step0 = (fun i j => raw36631 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36631step0 raw36631; decide +kernel
      have hl : raw36631step0Labels = raw36631Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36631 raw36631Labels permutation270 permutation7
    mixedMoment B raw36631step0 raw36631step0Labels = mixedMoment B raw36631step1 raw36631step1Labels := by
      have ha : raw36631step1 = -raw36631step0 := by apply Matrix.ext; change ∀ i j, raw36631step1 i j = -(raw36631step0 i j); unfold raw36631step1 raw36631step0; decide +kernel
      have hl : raw36631step1Labels = raw36631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36631step1 raw36631step1Labels = mixedMoment B raw36631step2 raw36631step2Labels := by
      have ha : raw36631step2 = raw36631step1 := by apply Matrix.ext; unfold raw36631step2 raw36631step1; decide +kernel
      have hl : raw36631step1Labels = labelEmbedding1 ∘ raw36631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36631step1 raw36631step1Labels raw36631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

def raw36632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36632step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw36632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw36632step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36632step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw36632step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36632 raw36632Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw36632 raw36632Labels = mixedMoment B raw36632step0 raw36632step0Labels := by
      have hz : ∀ j, raw36632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36632step0 = (fun i j => raw36632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36632step0 raw36632; decide +kernel
      have hl : raw36632step0Labels = raw36632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36632 raw36632Labels permutation346 hz
    mixedMoment B raw36632step0 raw36632step0Labels = mixedMoment B raw36632step1 raw36632step1Labels := by
      have ha : raw36632step1 = (fun i j => raw36632step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36632step1 raw36632step0; decide +kernel
      have hl : raw36632step1Labels = raw36632step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36632step0 raw36632step0Labels permutation34 permutation5
    mixedMoment B raw36632step1 raw36632step1Labels = mixedMoment B raw36632step2 raw36632step2Labels := by
      have ha : raw36632step2 = -raw36632step1 := by apply Matrix.ext; change ∀ i j, raw36632step2 i j = -(raw36632step1 i j); unfold raw36632step2 raw36632step1; decide +kernel
      have hl : raw36632step2Labels = raw36632step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36632step2 raw36632step2Labels = mixedMoment B raw36632step3 raw36632step3Labels := by
      have ha : raw36632step3 = raw36632step2 := by apply Matrix.ext; unfold raw36632step3 raw36632step2; decide +kernel
      have hl : raw36632step2Labels = labelEmbedding1 ∘ raw36632step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36632step2 raw36632step2Labels raw36632step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3591 node3591Labels := by rfl

def raw36633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36633step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36633step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36633 raw36633Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw36633 raw36633Labels = mixedMoment B raw36633step0 raw36633step0Labels := by
      have hz : ∀ j, raw36633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36633step0 = (fun i j => raw36633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36633step0 raw36633; decide +kernel
      have hl : raw36633step0Labels = raw36633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36633 raw36633Labels permutation346 hz
    mixedMoment B raw36633step0 raw36633step0Labels = mixedMoment B raw36633step1 raw36633step1Labels := by
      have ha : raw36633step1 = (fun i j => raw36633step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36633step1 raw36633step0; decide +kernel
      have hl : raw36633step1Labels = raw36633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36633step0 raw36633step0Labels permutation61 permutation7
    mixedMoment B raw36633step1 raw36633step1Labels = mixedMoment B raw36633step2 raw36633step2Labels := by
      have ha : raw36633step2 = -raw36633step1 := by apply Matrix.ext; change ∀ i j, raw36633step2 i j = -(raw36633step1 i j); unfold raw36633step2 raw36633step1; decide +kernel
      have hl : raw36633step2Labels = raw36633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36633step2 raw36633step2Labels = mixedMoment B raw36633step3 raw36633step3Labels := by
      have ha : raw36633step3 = raw36633step2 := by apply Matrix.ext; unfold raw36633step3 raw36633step2; decide +kernel
      have hl : raw36633step2Labels = labelEmbedding1 ∘ raw36633step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36633step2 raw36633step2Labels raw36633step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3417 node3417Labels := by rfl

def raw36634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36634step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36634 raw36634Labels = mixedMoment B node3754 node3754Labels := by
  calc
    mixedMoment B raw36634 raw36634Labels = mixedMoment B raw36634step0 raw36634step0Labels := by
      have ha : raw36634step0 = (fun i j => raw36634 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36634step0 raw36634; decide +kernel
      have hl : raw36634step0Labels = raw36634Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36634 raw36634Labels permutation270 permutation7
    mixedMoment B raw36634step0 raw36634step0Labels = mixedMoment B raw36634step1 raw36634step1Labels := by
      have ha : raw36634step1 = -raw36634step0 := by apply Matrix.ext; change ∀ i j, raw36634step1 i j = -(raw36634step0 i j); unfold raw36634step1 raw36634step0; decide +kernel
      have hl : raw36634step1Labels = raw36634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36634step1 raw36634step1Labels = mixedMoment B raw36634step2 raw36634step2Labels := by
      have ha : raw36634step2 = raw36634step1 := by apply Matrix.ext; unfold raw36634step2 raw36634step1; decide +kernel
      have hl : raw36634step1Labels = labelEmbedding1 ∘ raw36634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36634step1 raw36634step1Labels raw36634step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3754 node3754Labels := by rfl

def raw36635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36635step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36635step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36635 raw36635Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw36635 raw36635Labels = mixedMoment B raw36635step0 raw36635step0Labels := by
      have hz : ∀ j, raw36635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36635step0 = (fun i j => raw36635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36635step0 raw36635; decide +kernel
      have hl : raw36635step0Labels = raw36635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36635 raw36635Labels permutation346 hz
    mixedMoment B raw36635step0 raw36635step0Labels = mixedMoment B raw36635step1 raw36635step1Labels := by
      have ha : raw36635step1 = (fun i j => raw36635step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36635step1 raw36635step0; decide +kernel
      have hl : raw36635step1Labels = raw36635step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36635step0 raw36635step0Labels permutation61 permutation7
    mixedMoment B raw36635step1 raw36635step1Labels = mixedMoment B raw36635step2 raw36635step2Labels := by
      have ha : raw36635step2 = -raw36635step1 := by apply Matrix.ext; change ∀ i j, raw36635step2 i j = -(raw36635step1 i j); unfold raw36635step2 raw36635step1; decide +kernel
      have hl : raw36635step2Labels = raw36635step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36635step2 raw36635step2Labels = mixedMoment B raw36635step3 raw36635step3Labels := by
      have ha : raw36635step3 = raw36635step2 := by apply Matrix.ext; unfold raw36635step3 raw36635step2; decide +kernel
      have hl : raw36635step2Labels = labelEmbedding1 ∘ raw36635step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36635step2 raw36635step2Labels raw36635step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw36636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36636step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36636step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36636step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36636step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36636 raw36636Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw36636 raw36636Labels = mixedMoment B raw36636step0 raw36636step0Labels := by
      have hz : ∀ j, raw36636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36636step0 = (fun i j => raw36636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36636step0 raw36636; decide +kernel
      have hl : raw36636step0Labels = raw36636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36636 raw36636Labels permutation346 hz
    mixedMoment B raw36636step0 raw36636step0Labels = mixedMoment B raw36636step1 raw36636step1Labels := by
      have ha : raw36636step1 = (fun i j => raw36636step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36636step1 raw36636step0; decide +kernel
      have hl : raw36636step1Labels = raw36636step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36636step0 raw36636step0Labels permutation61 permutation7
    mixedMoment B raw36636step1 raw36636step1Labels = mixedMoment B raw36636step2 raw36636step2Labels := by
      have ha : raw36636step2 = -raw36636step1 := by apply Matrix.ext; change ∀ i j, raw36636step2 i j = -(raw36636step1 i j); unfold raw36636step2 raw36636step1; decide +kernel
      have hl : raw36636step2Labels = raw36636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36636step2 raw36636step2Labels = mixedMoment B raw36636step3 raw36636step3Labels := by
      have ha : raw36636step3 = raw36636step2 := by apply Matrix.ext; unfold raw36636step3 raw36636step2; decide +kernel
      have hl : raw36636step2Labels = labelEmbedding1 ∘ raw36636step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36636step2 raw36636step2Labels raw36636step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw36637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw36637step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36637step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36637step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36637step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36637 raw36637Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw36637 raw36637Labels = mixedMoment B raw36637step0 raw36637step0Labels := by
      have hz : ∀ j, raw36637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36637step0 = (fun i j => raw36637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36637step0 raw36637; decide +kernel
      have hl : raw36637step0Labels = raw36637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36637 raw36637Labels permutation346 hz
    mixedMoment B raw36637step0 raw36637step0Labels = mixedMoment B raw36637step1 raw36637step1Labels := by
      have ha : raw36637step1 = (fun i j => raw36637step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36637step1 raw36637step0; decide +kernel
      have hl : raw36637step1Labels = raw36637step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36637step0 raw36637step0Labels permutation38 permutation5
    mixedMoment B raw36637step1 raw36637step1Labels = mixedMoment B raw36637step2 raw36637step2Labels := by
      have ha : raw36637step2 = -raw36637step1 := by apply Matrix.ext; change ∀ i j, raw36637step2 i j = -(raw36637step1 i j); unfold raw36637step2 raw36637step1; decide +kernel
      have hl : raw36637step2Labels = raw36637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36637step2 raw36637step2Labels = mixedMoment B raw36637step3 raw36637step3Labels := by
      have ha : raw36637step3 = raw36637step2 := by apply Matrix.ext; unfold raw36637step3 raw36637step2; decide +kernel
      have hl : raw36637step2Labels = labelEmbedding1 ∘ raw36637step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36637step2 raw36637step2Labels raw36637step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

def raw36638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36638step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw36638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36638step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36638step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36638 raw36638Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw36638 raw36638Labels = mixedMoment B raw36638step0 raw36638step0Labels := by
      have hz : ∀ j, raw36638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36638step0 = (fun i j => raw36638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36638step0 raw36638; decide +kernel
      have hl : raw36638step0Labels = raw36638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36638 raw36638Labels permutation346 hz
    mixedMoment B raw36638step0 raw36638step0Labels = mixedMoment B raw36638step1 raw36638step1Labels := by
      have ha : raw36638step1 = (fun i j => raw36638step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36638step1 raw36638step0; decide +kernel
      have hl : raw36638step1Labels = raw36638step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36638step0 raw36638step0Labels permutation61 permutation7
    mixedMoment B raw36638step1 raw36638step1Labels = mixedMoment B raw36638step2 raw36638step2Labels := by
      have ha : raw36638step2 = -raw36638step1 := by apply Matrix.ext; change ∀ i j, raw36638step2 i j = -(raw36638step1 i j); unfold raw36638step2 raw36638step1; decide +kernel
      have hl : raw36638step2Labels = raw36638step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36638step2 raw36638step2Labels = mixedMoment B raw36638step3 raw36638step3Labels := by
      have ha : raw36638step3 = raw36638step2 := by apply Matrix.ext; unfold raw36638step3 raw36638step2; decide +kernel
      have hl : raw36638step2Labels = labelEmbedding1 ∘ raw36638step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36638step2 raw36638step2Labels raw36638step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

def raw36639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw36639step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36639step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36639step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36639 raw36639Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw36639 raw36639Labels = mixedMoment B raw36639step0 raw36639step0Labels := by
      have ha : raw36639step0 = (fun i j => raw36639 (permutation270 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36639step0 raw36639; decide +kernel
      have hl : raw36639step0Labels = raw36639Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36639 raw36639Labels permutation270 permutation7
    mixedMoment B raw36639step0 raw36639step0Labels = mixedMoment B raw36639step1 raw36639step1Labels := by
      have ha : raw36639step1 = -raw36639step0 := by apply Matrix.ext; change ∀ i j, raw36639step1 i j = -(raw36639step0 i j); unfold raw36639step1 raw36639step0; decide +kernel
      have hl : raw36639step1Labels = raw36639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36639step1 raw36639step1Labels = mixedMoment B raw36639step2 raw36639step2Labels := by
      have ha : raw36639step2 = raw36639step1 := by apply Matrix.ext; unfold raw36639step2 raw36639step1; decide +kernel
      have hl : raw36639step1Labels = labelEmbedding1 ∘ raw36639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36639step1 raw36639step1Labels raw36639step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

def raw36640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36640step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36640step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36640 raw36640Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw36640 raw36640Labels = mixedMoment B raw36640step0 raw36640step0Labels := by
      have hz : ∀ j, raw36640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36640step0 = (fun i j => raw36640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36640step0 raw36640; decide +kernel
      have hl : raw36640step0Labels = raw36640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36640 raw36640Labels permutation346 hz
    mixedMoment B raw36640step0 raw36640step0Labels = mixedMoment B raw36640step1 raw36640step1Labels := by
      have ha : raw36640step1 = (fun i j => raw36640step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36640step1 raw36640step0; decide +kernel
      have hl : raw36640step1Labels = raw36640step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36640step0 raw36640step0Labels permutation148 permutation5
    mixedMoment B raw36640step1 raw36640step1Labels = mixedMoment B raw36640step2 raw36640step2Labels := by
      have ha : raw36640step2 = raw36640step1 := by apply Matrix.ext; unfold raw36640step2 raw36640step1; decide +kernel
      have hl : raw36640step1Labels = labelEmbedding1 ∘ raw36640step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36640step1 raw36640step1Labels raw36640step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3772 node3772Labels := by rfl

def raw36641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw36641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw36641step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36641step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36641step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36641step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36641step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36641 raw36641Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw36641 raw36641Labels = mixedMoment B raw36641step0 raw36641step0Labels := by
      have hz : ∀ j, raw36641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36641step0 = (fun i j => raw36641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36641step0 raw36641; decide +kernel
      have hl : raw36641step0Labels = raw36641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36641 raw36641Labels permutation346 hz
    mixedMoment B raw36641step0 raw36641step0Labels = mixedMoment B raw36641step1 raw36641step1Labels := by
      have ha : raw36641step1 = (fun i j => raw36641step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36641step1 raw36641step0; decide +kernel
      have hl : raw36641step1Labels = raw36641step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36641step0 raw36641step0Labels permutation61 permutation7
    mixedMoment B raw36641step1 raw36641step1Labels = mixedMoment B raw36641step2 raw36641step2Labels := by
      have ha : raw36641step2 = -raw36641step1 := by apply Matrix.ext; change ∀ i j, raw36641step2 i j = -(raw36641step1 i j); unfold raw36641step2 raw36641step1; decide +kernel
      have hl : raw36641step2Labels = raw36641step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36641step2 raw36641step2Labels = mixedMoment B raw36641step3 raw36641step3Labels := by
      have ha : raw36641step3 = raw36641step2 := by apply Matrix.ext; unfold raw36641step3 raw36641step2; decide +kernel
      have hl : raw36641step2Labels = labelEmbedding1 ∘ raw36641step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36641step2 raw36641step2Labels raw36641step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

def raw36642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw36642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw36642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36642 raw36642Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw36642 raw36642Labels = mixedMoment B raw36642step0 raw36642step0Labels := by
      have hz : ∀ j, raw36642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36642step0 = (fun i j => raw36642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36642step0 raw36642; decide +kernel
      have hl : raw36642step0Labels = raw36642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36642 raw36642Labels permutation346 hz
    mixedMoment B raw36642step0 raw36642step0Labels = mixedMoment B raw36642step1 raw36642step1Labels := by
      have ha : raw36642step1 = (fun i j => raw36642step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36642step1 raw36642step0; decide +kernel
      have hl : raw36642step1Labels = raw36642step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36642step0 raw36642step0Labels permutation149 permutation5
    mixedMoment B raw36642step1 raw36642step1Labels = mixedMoment B raw36642step2 raw36642step2Labels := by
      have ha : raw36642step2 = raw36642step1 := by apply Matrix.ext; unfold raw36642step2 raw36642step1; decide +kernel
      have hl : raw36642step1Labels = labelEmbedding1 ∘ raw36642step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36642step1 raw36642step1Labels raw36642step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

def raw36643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36643step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw36643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw36643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36643 raw36643Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw36643 raw36643Labels = mixedMoment B raw36643step0 raw36643step0Labels := by
      have hz : ∀ j, raw36643 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36643step0 = (fun i j => raw36643 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36643step0 raw36643; decide +kernel
      have hl : raw36643step0Labels = raw36643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36643 raw36643Labels permutation346 hz
    mixedMoment B raw36643step0 raw36643step0Labels = mixedMoment B raw36643step1 raw36643step1Labels := by
      have ha : raw36643step1 = (fun i j => raw36643step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36643step1 raw36643step0; decide +kernel
      have hl : raw36643step1Labels = raw36643step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36643step0 raw36643step0Labels permutation150 permutation5
    mixedMoment B raw36643step1 raw36643step1Labels = mixedMoment B raw36643step2 raw36643step2Labels := by
      have ha : raw36643step2 = raw36643step1 := by apply Matrix.ext; unfold raw36643step2 raw36643step1; decide +kernel
      have hl : raw36643step1Labels = labelEmbedding1 ∘ raw36643step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36643step1 raw36643step1Labels raw36643step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw36644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36644 raw36644Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw36644 raw36644Labels = mixedMoment B raw36644step0 raw36644step0Labels := by
      have ha : raw36644step0 = (fun i j => raw36644 (permutation676 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36644step0 raw36644; decide +kernel
      have hl : raw36644step0Labels = raw36644Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36644 raw36644Labels permutation676 permutation5
    mixedMoment B raw36644step0 raw36644step0Labels = mixedMoment B raw36644step1 raw36644step1Labels := by
      have ha : raw36644step1 = raw36644step0 := by apply Matrix.ext; unfold raw36644step1 raw36644step0; decide +kernel
      have hl : raw36644step0Labels = labelEmbedding1 ∘ raw36644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36644step0 raw36644step0Labels raw36644step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

def raw36645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36645step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36645step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36645 raw36645Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw36645 raw36645Labels = mixedMoment B raw36645step0 raw36645step0Labels := by
      have hz : ∀ j, raw36645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36645step0 = (fun i j => raw36645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36645step0 raw36645; decide +kernel
      have hl : raw36645step0Labels = raw36645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36645 raw36645Labels permutation346 hz
    mixedMoment B raw36645step0 raw36645step0Labels = mixedMoment B raw36645step1 raw36645step1Labels := by
      have ha : raw36645step1 = (fun i j => raw36645step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36645step1 raw36645step0; decide +kernel
      have hl : raw36645step1Labels = raw36645step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36645step0 raw36645step0Labels permutation148 permutation5
    mixedMoment B raw36645step1 raw36645step1Labels = mixedMoment B raw36645step2 raw36645step2Labels := by
      have ha : raw36645step2 = raw36645step1 := by apply Matrix.ext; unfold raw36645step2 raw36645step1; decide +kernel
      have hl : raw36645step1Labels = labelEmbedding1 ∘ raw36645step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36645step1 raw36645step1Labels raw36645step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw36646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw36646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw36646step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw36646step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw36646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36646 raw36646Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw36646 raw36646Labels = mixedMoment B raw36646step0 raw36646step0Labels := by
      have hz : ∀ j, raw36646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36646step0 = (fun i j => raw36646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36646step0 raw36646; decide +kernel
      have hl : raw36646step0Labels = raw36646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36646 raw36646Labels permutation346 hz
    mixedMoment B raw36646step0 raw36646step0Labels = mixedMoment B raw36646step1 raw36646step1Labels := by
      have ha : raw36646step1 = (fun i j => raw36646step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36646step1 raw36646step0; decide +kernel
      have hl : raw36646step1Labels = raw36646step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36646step0 raw36646step0Labels permutation137 permutation5
    mixedMoment B raw36646step1 raw36646step1Labels = mixedMoment B raw36646step2 raw36646step2Labels := by
      have ha : raw36646step2 = raw36646step1 := by apply Matrix.ext; unfold raw36646step2 raw36646step1; decide +kernel
      have hl : raw36646step1Labels = labelEmbedding1 ∘ raw36646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36646step1 raw36646step1Labels raw36646step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw36647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 3, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36647step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36647step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36647 raw36647Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw36647 raw36647Labels = mixedMoment B raw36647step0 raw36647step0Labels := by
      have hz : ∀ j, raw36647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36647step0 = (fun i j => raw36647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36647step0 raw36647; decide +kernel
      have hl : raw36647step0Labels = raw36647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36647 raw36647Labels permutation346 hz
    mixedMoment B raw36647step0 raw36647step0Labels = mixedMoment B raw36647step1 raw36647step1Labels := by
      have ha : raw36647step1 = (fun i j => raw36647step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36647step1 raw36647step0; decide +kernel
      have hl : raw36647step1Labels = raw36647step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36647step0 raw36647step0Labels permutation58 permutation3
    mixedMoment B raw36647step1 raw36647step1Labels = mixedMoment B raw36647step2 raw36647step2Labels := by
      have ha : raw36647step2 = raw36647step1 := by apply Matrix.ext; unfold raw36647step2 raw36647step1; decide +kernel
      have hl : raw36647step1Labels = labelEmbedding6 ∘ raw36647step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36647step1 raw36647step1Labels raw36647step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw36648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36648step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36648 raw36648Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw36648 raw36648Labels = mixedMoment B raw36648step0 raw36648step0Labels := by
      have ha : raw36648step0 = (fun i j => raw36648 (permutation291 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36648step0 raw36648; decide +kernel
      have hl : raw36648step0Labels = raw36648Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36648 raw36648Labels permutation291 permutation3
    mixedMoment B raw36648step0 raw36648step0Labels = mixedMoment B raw36648step1 raw36648step1Labels := by
      have ha : raw36648step1 = raw36648step0 := by apply Matrix.ext; unfold raw36648step1 raw36648step0; decide +kernel
      have hl : raw36648step0Labels = labelEmbedding6 ∘ raw36648step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36648step0 raw36648step0Labels raw36648step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw36649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw36649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36649 raw36649Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw36649 raw36649Labels = mixedMoment B raw36649step0 raw36649step0Labels := by
      have hz : ∀ j, raw36649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36649step0 = (fun i j => raw36649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36649step0 raw36649; decide +kernel
      have hl : raw36649step0Labels = raw36649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36649 raw36649Labels permutation346 hz
    mixedMoment B raw36649step0 raw36649step0Labels = mixedMoment B raw36649step1 raw36649step1Labels := by
      have ha : raw36649step1 = (fun i j => raw36649step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36649step1 raw36649step0; decide +kernel
      have hl : raw36649step1Labels = raw36649step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36649step0 raw36649step0Labels permutation150 permutation2
    mixedMoment B raw36649step1 raw36649step1Labels = mixedMoment B raw36649step2 raw36649step2Labels := by
      have ha : raw36649step2 = -raw36649step1 := by apply Matrix.ext; change ∀ i j, raw36649step2 i j = -(raw36649step1 i j); unfold raw36649step2 raw36649step1; decide +kernel
      have hl : raw36649step2Labels = raw36649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw36650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw36650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw36650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2]]
def raw36650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36650step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36650step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36650 raw36650Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw36650 raw36650Labels = mixedMoment B raw36650step0 raw36650step0Labels := by
      have hz : ∀ j, raw36650 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36650step0 = (fun i j => raw36650 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36650step0 raw36650; decide +kernel
      have hl : raw36650step0Labels = raw36650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36650 raw36650Labels permutation520 hz
    mixedMoment B raw36650step0 raw36650step0Labels = mixedMoment B raw36650step1 raw36650step1Labels := by
      have hz : ∀ j, raw36650step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36650step1 = (fun i j => raw36650step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36650step1 raw36650step0; decide +kernel
      have hl : raw36650step1Labels = raw36650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36650step0 raw36650step0Labels permutation80 hz
    mixedMoment B raw36650step1 raw36650step1Labels = mixedMoment B raw36650step2 raw36650step2Labels := by
      have ha : raw36650step2 = (fun i j => raw36650step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36650step2 raw36650step1; decide +kernel
      have hl : raw36650step2Labels = raw36650step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36650step1 raw36650step1Labels permutation14 permutation3
    mixedMoment B raw36650step2 raw36650step2Labels = mixedMoment B raw36650step3 raw36650step3Labels := by
      have ha : raw36650step3 = raw36650step2 := by apply Matrix.ext; unfold raw36650step3 raw36650step2; decide +kernel
      have hl : raw36650step2Labels = labelEmbedding6 ∘ raw36650step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36650step2 raw36650step2Labels raw36650step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw36651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36651step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36651 raw36651Labels = mixedMoment B node4648 node4648Labels := by
  calc
    mixedMoment B raw36651 raw36651Labels = mixedMoment B raw36651step0 raw36651step0Labels := by
      have ha : raw36651step0 = (fun i j => raw36651 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36651step0 raw36651; decide +kernel
      have hl : raw36651step0Labels = raw36651Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36651 raw36651Labels permutation267 permutation3
    mixedMoment B raw36651step0 raw36651step0Labels = mixedMoment B raw36651step1 raw36651step1Labels := by
      have ha : raw36651step1 = raw36651step0 := by apply Matrix.ext; unfold raw36651step1 raw36651step0; decide +kernel
      have hl : raw36651step0Labels = labelEmbedding6 ∘ raw36651step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36651step0 raw36651step0Labels raw36651step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4648 node4648Labels := by rfl

def raw36652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36652step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36652 raw36652Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw36652 raw36652Labels = mixedMoment B raw36652step0 raw36652step0Labels := by
      have ha : raw36652step0 = (fun i j => raw36652 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36652step0 raw36652; decide +kernel
      have hl : raw36652step0Labels = raw36652Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36652 raw36652Labels permutation271 permutation3
    mixedMoment B raw36652step0 raw36652step0Labels = mixedMoment B raw36652step1 raw36652step1Labels := by
      have ha : raw36652step1 = raw36652step0 := by apply Matrix.ext; unfold raw36652step1 raw36652step0; decide +kernel
      have hl : raw36652step0Labels = labelEmbedding6 ∘ raw36652step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36652step0 raw36652step0Labels raw36652step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw36653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw36653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw36653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36653step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36653 raw36653Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw36653 raw36653Labels = mixedMoment B raw36653step0 raw36653step0Labels := by
      have hz : ∀ j, raw36653 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36653step0 = (fun i j => raw36653 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36653step0 raw36653; decide +kernel
      have hl : raw36653step0Labels = raw36653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36653 raw36653Labels permutation520 hz
    mixedMoment B raw36653step0 raw36653step0Labels = mixedMoment B raw36653step1 raw36653step1Labels := by
      have ha : raw36653step1 = (fun i j => raw36653step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36653step1 raw36653step0; decide +kernel
      have hl : raw36653step1Labels = raw36653step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36653step0 raw36653step0Labels permutation56 permutation3
    mixedMoment B raw36653step1 raw36653step1Labels = mixedMoment B raw36653step2 raw36653step2Labels := by
      have ha : raw36653step2 = raw36653step1 := by apply Matrix.ext; unfold raw36653step2 raw36653step1; decide +kernel
      have hl : raw36653step1Labels = labelEmbedding6 ∘ raw36653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36653step1 raw36653step1Labels raw36653step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw36654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw36654step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw36654step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36654 raw36654Labels = mixedMoment B node4651 node4651Labels := by
  calc
    mixedMoment B raw36654 raw36654Labels = mixedMoment B raw36654step0 raw36654step0Labels := by
      have hz : ∀ j, raw36654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36654step0 = (fun i j => raw36654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36654step0 raw36654; decide +kernel
      have hl : raw36654step0Labels = raw36654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36654 raw36654Labels permutation346 hz
    mixedMoment B raw36654step0 raw36654step0Labels = mixedMoment B raw36654step1 raw36654step1Labels := by
      have ha : raw36654step1 = (fun i j => raw36654step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36654step1 raw36654step0; decide +kernel
      have hl : raw36654step1Labels = raw36654step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36654step0 raw36654step0Labels permutation59 permutation3
    mixedMoment B raw36654step1 raw36654step1Labels = mixedMoment B raw36654step2 raw36654step2Labels := by
      have ha : raw36654step2 = raw36654step1 := by apply Matrix.ext; unfold raw36654step2 raw36654step1; decide +kernel
      have hl : raw36654step1Labels = labelEmbedding6 ∘ raw36654step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36654step1 raw36654step1Labels raw36654step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4651 node4651Labels := by rfl

def raw36655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36655step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36655 raw36655Labels = mixedMoment B node5046 node5046Labels := by
  calc
    mixedMoment B raw36655 raw36655Labels = mixedMoment B raw36655step0 raw36655step0Labels := by
      have ha : raw36655step0 = (fun i j => raw36655 (permutation503 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36655step0 raw36655; decide +kernel
      have hl : raw36655step0Labels = raw36655Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36655 raw36655Labels permutation503 permutation5
    mixedMoment B raw36655step0 raw36655step0Labels = mixedMoment B raw36655step1 raw36655step1Labels := by
      have ha : raw36655step1 = raw36655step0 := by apply Matrix.ext; unfold raw36655step1 raw36655step0; decide +kernel
      have hl : raw36655step0Labels = labelEmbedding8 ∘ raw36655step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36655step0 raw36655step0Labels raw36655step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5046 node5046Labels := by rfl

def raw36656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![2, 0, -2]]
def raw36656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw36656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -3, 1], ![2, 0, -2]]
def raw36656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36656step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36656step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36656 raw36656Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw36656 raw36656Labels = mixedMoment B raw36656step0 raw36656step0Labels := by
      have hz : ∀ j, raw36656 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36656step0 = (fun i j => raw36656 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36656step0 raw36656; decide +kernel
      have hl : raw36656step0Labels = raw36656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36656 raw36656Labels permutation520 hz
    mixedMoment B raw36656step0 raw36656step0Labels = mixedMoment B raw36656step1 raw36656step1Labels := by
      have hz : ∀ j, raw36656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36656step1 = (fun i j => raw36656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36656step1 raw36656step0; decide +kernel
      have hl : raw36656step1Labels = raw36656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36656step0 raw36656step0Labels permutation80 hz
    mixedMoment B raw36656step1 raw36656step1Labels = mixedMoment B raw36656step2 raw36656step2Labels := by
      have ha : raw36656step2 = (fun i j => raw36656step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36656step2 raw36656step1; decide +kernel
      have hl : raw36656step2Labels = raw36656step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36656step1 raw36656step1Labels permutation24 permutation5
    mixedMoment B raw36656step2 raw36656step2Labels = mixedMoment B raw36656step3 raw36656step3Labels := by
      have ha : raw36656step3 = raw36656step2 := by apply Matrix.ext; unfold raw36656step3 raw36656step2; decide +kernel
      have hl : raw36656step2Labels = labelEmbedding8 ∘ raw36656step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36656step2 raw36656step2Labels raw36656step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw36657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw36657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw36657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36657step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36657step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36657 raw36657Labels = mixedMoment B node4653 node4653Labels := by
  calc
    mixedMoment B raw36657 raw36657Labels = mixedMoment B raw36657step0 raw36657step0Labels := by
      have hz : ∀ j, raw36657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36657step0 = (fun i j => raw36657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36657step0 raw36657; decide +kernel
      have hl : raw36657step0Labels = raw36657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36657 raw36657Labels permutation346 hz
    mixedMoment B raw36657step0 raw36657step0Labels = mixedMoment B raw36657step1 raw36657step1Labels := by
      have ha : raw36657step1 = (fun i j => raw36657step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36657step1 raw36657step0; decide +kernel
      have hl : raw36657step1Labels = raw36657step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36657step0 raw36657step0Labels permutation57 permutation3
    mixedMoment B raw36657step1 raw36657step1Labels = mixedMoment B raw36657step2 raw36657step2Labels := by
      have ha : raw36657step2 = raw36657step1 := by apply Matrix.ext; unfold raw36657step2 raw36657step1; decide +kernel
      have hl : raw36657step1Labels = labelEmbedding6 ∘ raw36657step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36657step1 raw36657step1Labels raw36657step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4653 node4653Labels := by rfl

def raw36658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw36658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36658step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36658 raw36658Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw36658 raw36658Labels = mixedMoment B raw36658step0 raw36658step0Labels := by
      have ha : raw36658step0 = (fun i j => raw36658 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36658step0 raw36658; decide +kernel
      have hl : raw36658step0Labels = raw36658Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36658 raw36658Labels permutation266 permutation3
    mixedMoment B raw36658step0 raw36658step0Labels = mixedMoment B raw36658step1 raw36658step1Labels := by
      have ha : raw36658step1 = raw36658step0 := by apply Matrix.ext; unfold raw36658step1 raw36658step0; decide +kernel
      have hl : raw36658step0Labels = labelEmbedding6 ∘ raw36658step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36658step0 raw36658step0Labels raw36658step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

def raw36659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw36659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw36659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36659step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36659step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36659 raw36659Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw36659 raw36659Labels = mixedMoment B raw36659step0 raw36659step0Labels := by
      have hz : ∀ j, raw36659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36659step0 = (fun i j => raw36659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36659step0 raw36659; decide +kernel
      have hl : raw36659step0Labels = raw36659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36659 raw36659Labels permutation346 hz
    mixedMoment B raw36659step0 raw36659step0Labels = mixedMoment B raw36659step1 raw36659step1Labels := by
      have ha : raw36659step1 = (fun i j => raw36659step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36659step1 raw36659step0; decide +kernel
      have hl : raw36659step1Labels = raw36659step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36659step0 raw36659step0Labels permutation57 permutation3
    mixedMoment B raw36659step1 raw36659step1Labels = mixedMoment B raw36659step2 raw36659step2Labels := by
      have ha : raw36659step2 = raw36659step1 := by apply Matrix.ext; unfold raw36659step2 raw36659step1; decide +kernel
      have hl : raw36659step1Labels = labelEmbedding6 ∘ raw36659step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36659step1 raw36659step1Labels raw36659step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw36660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw36660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw36660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw36660step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw36660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36660 raw36660Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw36660 raw36660Labels = mixedMoment B raw36660step0 raw36660step0Labels := by
      have hz : ∀ j, raw36660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36660step0 = (fun i j => raw36660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36660step0 raw36660; decide +kernel
      have hl : raw36660step0Labels = raw36660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36660 raw36660Labels permutation346 hz
    mixedMoment B raw36660step0 raw36660step0Labels = mixedMoment B raw36660step1 raw36660step1Labels := by
      have ha : raw36660step1 = (fun i j => raw36660step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36660step1 raw36660step0; decide +kernel
      have hl : raw36660step1Labels = raw36660step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36660step0 raw36660step0Labels permutation58 permutation3
    mixedMoment B raw36660step1 raw36660step1Labels = mixedMoment B raw36660step2 raw36660step2Labels := by
      have ha : raw36660step2 = raw36660step1 := by apply Matrix.ext; unfold raw36660step2 raw36660step1; decide +kernel
      have hl : raw36660step1Labels = labelEmbedding6 ∘ raw36660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36660step1 raw36660step1Labels raw36660step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

def raw36661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw36661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 1, 1]]
def raw36661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36661 raw36661Labels = mixedMoment B node5119 node5119Labels := by
  calc
    mixedMoment B raw36661 raw36661Labels = mixedMoment B raw36661step0 raw36661step0Labels := by
      have ha : raw36661step0 = (fun i j => raw36661 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36661step0 raw36661; decide +kernel
      have hl : raw36661step0Labels = raw36661Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36661 raw36661Labels permutation688 permutation2
    mixedMoment B raw36661step0 raw36661step0Labels = mixedMoment B raw36661step1 raw36661step1Labels := by
      have ha : raw36661step1 = -raw36661step0 := by apply Matrix.ext; change ∀ i j, raw36661step1 i j = -(raw36661step0 i j); unfold raw36661step1 raw36661step0; decide +kernel
      have hl : raw36661step1Labels = raw36661step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5119 node5119Labels := by rfl

def raw36662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw36662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw36662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36662 raw36662Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw36662 raw36662Labels = mixedMoment B raw36662step0 raw36662step0Labels := by
      have hz : ∀ j, raw36662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36662step0 = (fun i j => raw36662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36662step0 raw36662; decide +kernel
      have hl : raw36662step0Labels = raw36662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36662 raw36662Labels permutation346 hz
    mixedMoment B raw36662step0 raw36662step0Labels = mixedMoment B raw36662step1 raw36662step1Labels := by
      have ha : raw36662step1 = (fun i j => raw36662step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36662step1 raw36662step0; decide +kernel
      have hl : raw36662step1Labels = raw36662step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36662step0 raw36662step0Labels permutation151 permutation2
    mixedMoment B raw36662step1 raw36662step1Labels = mixedMoment B raw36662step2 raw36662step2Labels := by
      have ha : raw36662step2 = -raw36662step1 := by apply Matrix.ext; change ∀ i j, raw36662step2 i j = -(raw36662step1 i j); unfold raw36662step2 raw36662step1; decide +kernel
      have hl : raw36662step2Labels = raw36662step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw36663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, -1, -2]]
def raw36663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw36663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![3, -1, -2]]
def raw36663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36663step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36663 raw36663Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw36663 raw36663Labels = mixedMoment B raw36663step0 raw36663step0Labels := by
      have hz : ∀ j, raw36663 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36663step0 = (fun i j => raw36663 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36663step0 raw36663; decide +kernel
      have hl : raw36663step0Labels = raw36663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36663 raw36663Labels permutation520 hz
    mixedMoment B raw36663step0 raw36663step0Labels = mixedMoment B raw36663step1 raw36663step1Labels := by
      have hz : ∀ j, raw36663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36663step1 = (fun i j => raw36663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36663step1 raw36663step0; decide +kernel
      have hl : raw36663step1Labels = raw36663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36663step0 raw36663step0Labels permutation80 hz
    mixedMoment B raw36663step1 raw36663step1Labels = mixedMoment B raw36663step2 raw36663step2Labels := by
      have ha : raw36663step2 = (fun i j => raw36663step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36663step2 raw36663step1; decide +kernel
      have hl : raw36663step2Labels = raw36663step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36663step1 raw36663step1Labels permutation31 permutation2
    mixedMoment B raw36663step2 raw36663step2Labels = mixedMoment B raw36663step3 raw36663step3Labels := by
      have ha : raw36663step3 = -raw36663step2 := by apply Matrix.ext; change ∀ i j, raw36663step3 i j = -(raw36663step2 i j); unfold raw36663step3 raw36663step2; decide +kernel
      have hl : raw36663step3Labels = raw36663step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw36664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36664 raw36664Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw36664 raw36664Labels = mixedMoment B raw36664step0 raw36664step0Labels := by
      have hz : ∀ j, raw36664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36664step0 = (fun i j => raw36664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36664step0 raw36664; decide +kernel
      have hl : raw36664step0Labels = raw36664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36664 raw36664Labels permutation346 hz
    mixedMoment B raw36664step0 raw36664step0Labels = mixedMoment B raw36664step1 raw36664step1Labels := by
      have ha : raw36664step1 = (fun i j => raw36664step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36664step1 raw36664step0; decide +kernel
      have hl : raw36664step1Labels = raw36664step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36664step0 raw36664step0Labels permutation58 permutation2
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw36665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36665 raw36665Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw36665 raw36665Labels = mixedMoment B raw36665step0 raw36665step0Labels := by
      have ha : raw36665step0 = (fun i j => raw36665 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36665step0 raw36665; decide +kernel
      have hl : raw36665step0Labels = raw36665Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36665 raw36665Labels permutation267 permutation2
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw36666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36666step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36666step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36666step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36666step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36666 raw36666Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw36666 raw36666Labels = mixedMoment B raw36666step0 raw36666step0Labels := by
      have hz : ∀ j, raw36666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36666step0 = (fun i j => raw36666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36666step0 raw36666; decide +kernel
      have hl : raw36666step0Labels = raw36666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36666 raw36666Labels permutation346 hz
    mixedMoment B raw36666step0 raw36666step0Labels = mixedMoment B raw36666step1 raw36666step1Labels := by
      have ha : raw36666step1 = (fun i j => raw36666step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36666step1 raw36666step0; decide +kernel
      have hl : raw36666step1Labels = raw36666step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36666step0 raw36666step0Labels permutation59 permutation7
    mixedMoment B raw36666step1 raw36666step1Labels = mixedMoment B raw36666step2 raw36666step2Labels := by
      have ha : raw36666step2 = -raw36666step1 := by apply Matrix.ext; change ∀ i j, raw36666step2 i j = -(raw36666step1 i j); unfold raw36666step2 raw36666step1; decide +kernel
      have hl : raw36666step2Labels = raw36666step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36666step2 raw36666step2Labels = mixedMoment B raw36666step3 raw36666step3Labels := by
      have ha : raw36666step3 = raw36666step2 := by apply Matrix.ext; unfold raw36666step3 raw36666step2; decide +kernel
      have hl : raw36666step2Labels = labelEmbedding10 ∘ raw36666step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36666step2 raw36666step2Labels raw36666step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw36667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1]]
def raw36667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36667 raw36667Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw36667 raw36667Labels = mixedMoment B raw36667step0 raw36667step0Labels := by
      have hz : ∀ j, raw36667 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36667step0 = (fun i j => raw36667 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36667step0 raw36667; decide +kernel
      have hl : raw36667step0Labels = raw36667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36667 raw36667Labels permutation520 hz
    mixedMoment B raw36667step0 raw36667step0Labels = mixedMoment B raw36667step1 raw36667step1Labels := by
      have hz : ∀ j, raw36667step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36667step1 = (fun i j => raw36667step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36667step1 raw36667step0; decide +kernel
      have hl : raw36667step1Labels = raw36667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36667step0 raw36667step0Labels permutation80 hz
    mixedMoment B raw36667step1 raw36667step1Labels = mixedMoment B raw36667step2 raw36667step2Labels := by
      have ha : raw36667step2 = (fun i j => raw36667step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36667step2 raw36667step1; decide +kernel
      have hl : raw36667step2Labels = raw36667step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36667step1 raw36667step1Labels permutation14 permutation2
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw36668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36668step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36668step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36668step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36668step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36668 raw36668Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw36668 raw36668Labels = mixedMoment B raw36668step0 raw36668step0Labels := by
      have hz : ∀ j, raw36668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36668step0 = (fun i j => raw36668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36668step0 raw36668; decide +kernel
      have hl : raw36668step0Labels = raw36668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36668 raw36668Labels permutation346 hz
    mixedMoment B raw36668step0 raw36668step0Labels = mixedMoment B raw36668step1 raw36668step1Labels := by
      have ha : raw36668step1 = (fun i j => raw36668step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36668step1 raw36668step0; decide +kernel
      have hl : raw36668step1Labels = raw36668step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36668step0 raw36668step0Labels permutation59 permutation7
    mixedMoment B raw36668step1 raw36668step1Labels = mixedMoment B raw36668step2 raw36668step2Labels := by
      have ha : raw36668step2 = -raw36668step1 := by apply Matrix.ext; change ∀ i j, raw36668step2 i j = -(raw36668step1 i j); unfold raw36668step2 raw36668step1; decide +kernel
      have hl : raw36668step2Labels = raw36668step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36668step2 raw36668step2Labels = mixedMoment B raw36668step3 raw36668step3Labels := by
      have ha : raw36668step3 = raw36668step2 := by apply Matrix.ext; unfold raw36668step3 raw36668step2; decide +kernel
      have hl : raw36668step2Labels = labelEmbedding10 ∘ raw36668step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36668step2 raw36668step2Labels raw36668step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw36669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36669step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36669 raw36669Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw36669 raw36669Labels = mixedMoment B raw36669step0 raw36669step0Labels := by
      have hz : ∀ j, raw36669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36669step0 = (fun i j => raw36669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36669step0 raw36669; decide +kernel
      have hl : raw36669step0Labels = raw36669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36669 raw36669Labels permutation346 hz
    mixedMoment B raw36669step0 raw36669step0Labels = mixedMoment B raw36669step1 raw36669step1Labels := by
      have ha : raw36669step1 = (fun i j => raw36669step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36669step1 raw36669step0; decide +kernel
      have hl : raw36669step1Labels = raw36669step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36669step0 raw36669step0Labels permutation32 permutation3
    mixedMoment B raw36669step1 raw36669step1Labels = mixedMoment B raw36669step2 raw36669step2Labels := by
      have ha : raw36669step2 = raw36669step1 := by apply Matrix.ext; unfold raw36669step2 raw36669step1; decide +kernel
      have hl : raw36669step1Labels = labelEmbedding6 ∘ raw36669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36669step1 raw36669step1Labels raw36669step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw36670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36670 raw36670Labels = mixedMoment B node5468 node5468Labels := by
  calc
    mixedMoment B raw36670 raw36670Labels = mixedMoment B raw36670step0 raw36670step0Labels := by
      have ha : raw36670step0 = (fun i j => raw36670 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36670step0 raw36670; decide +kernel
      have hl : raw36670step0Labels = raw36670Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36670 raw36670Labels permutation154 permutation2
    _ = mixedMoment B node5468 node5468Labels := by rfl

def raw36671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw36671step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw36671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36671 raw36671Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw36671 raw36671Labels = mixedMoment B raw36671step0 raw36671step0Labels := by
      have hz : ∀ j, raw36671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36671step0 = (fun i j => raw36671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36671step0 raw36671; decide +kernel
      have hl : raw36671step0Labels = raw36671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36671 raw36671Labels permutation346 hz
    mixedMoment B raw36671step0 raw36671step0Labels = mixedMoment B raw36671step1 raw36671step1Labels := by
      have ha : raw36671step1 = (fun i j => raw36671step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36671step1 raw36671step0; decide +kernel
      have hl : raw36671step1Labels = raw36671step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36671step0 raw36671step0Labels permutation102 permutation6
    mixedMoment B raw36671step1 raw36671step1Labels = mixedMoment B raw36671step2 raw36671step2Labels := by
      have ha : raw36671step2 = raw36671step1 := by apply Matrix.ext; unfold raw36671step2 raw36671step1; decide +kernel
      have hl : raw36671step1Labels = labelEmbedding9 ∘ raw36671step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36671step1 raw36671step1Labels raw36671step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw36672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw36672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36672 raw36672Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw36672 raw36672Labels = mixedMoment B raw36672step0 raw36672step0Labels := by
      have hz : ∀ j, raw36672 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36672step0 = (fun i j => raw36672 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36672step0 raw36672; decide +kernel
      have hl : raw36672step0Labels = raw36672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36672 raw36672Labels permutation520 hz
    mixedMoment B raw36672step0 raw36672step0Labels = mixedMoment B raw36672step1 raw36672step1Labels := by
      have hz : ∀ j, raw36672step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36672step1 = (fun i j => raw36672step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36672step1 raw36672step0; decide +kernel
      have hl : raw36672step1Labels = raw36672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36672step0 raw36672step0Labels permutation80 hz
    _ = mixedMoment B node5475 node5475Labels := by rfl

def raw36673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36673step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36673step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36673step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36673 raw36673Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw36673 raw36673Labels = mixedMoment B raw36673step0 raw36673step0Labels := by
      have hz : ∀ j, raw36673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36673step0 = (fun i j => raw36673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36673step0 raw36673; decide +kernel
      have hl : raw36673step0Labels = raw36673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36673 raw36673Labels permutation346 hz
    mixedMoment B raw36673step0 raw36673step0Labels = mixedMoment B raw36673step1 raw36673step1Labels := by
      have ha : raw36673step1 = (fun i j => raw36673step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36673step1 raw36673step0; decide +kernel
      have hl : raw36673step1Labels = raw36673step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36673step0 raw36673step0Labels permutation59 permutation7
    mixedMoment B raw36673step1 raw36673step1Labels = mixedMoment B raw36673step2 raw36673step2Labels := by
      have ha : raw36673step2 = -raw36673step1 := by apply Matrix.ext; change ∀ i j, raw36673step2 i j = -(raw36673step1 i j); unfold raw36673step2 raw36673step1; decide +kernel
      have hl : raw36673step2Labels = raw36673step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36673step2 raw36673step2Labels = mixedMoment B raw36673step3 raw36673step3Labels := by
      have ha : raw36673step3 = raw36673step2 := by apply Matrix.ext; unfold raw36673step3 raw36673step2; decide +kernel
      have hl : raw36673step2Labels = labelEmbedding10 ∘ raw36673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36673step2 raw36673step2Labels raw36673step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw36674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36674step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36674 raw36674Labels = mixedMoment B node4964 node4964Labels := by
  calc
    mixedMoment B raw36674 raw36674Labels = mixedMoment B raw36674step0 raw36674step0Labels := by
      have ha : raw36674step0 = (fun i j => raw36674 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36674step0 raw36674; decide +kernel
      have hl : raw36674step0Labels = raw36674Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36674 raw36674Labels permutation158 permutation3
    mixedMoment B raw36674step0 raw36674step0Labels = mixedMoment B raw36674step1 raw36674step1Labels := by
      have ha : raw36674step1 = raw36674step0 := by apply Matrix.ext; unfold raw36674step1 raw36674step0; decide +kernel
      have hl : raw36674step0Labels = labelEmbedding6 ∘ raw36674step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36674step0 raw36674step0Labels raw36674step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4964 node4964Labels := by rfl

def raw36675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36675 raw36675Labels = mixedMoment B node4940 node4940Labels := by
  calc
    mixedMoment B raw36675 raw36675Labels = mixedMoment B raw36675step0 raw36675step0Labels := by
      have ha : raw36675step0 = (fun i j => raw36675 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36675step0 raw36675; decide +kernel
      have hl : raw36675step0Labels = raw36675Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36675 raw36675Labels permutation267 permutation2
    _ = mixedMoment B node4940 node4940Labels := by rfl

def raw36676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36676 raw36676Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw36676 raw36676Labels = mixedMoment B raw36676step0 raw36676step0Labels := by
      have ha : raw36676step0 = (fun i j => raw36676 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36676step0 raw36676; decide +kernel
      have hl : raw36676step0Labels = raw36676Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36676 raw36676Labels permutation271 permutation2
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw36677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36677 raw36677Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw36677 raw36677Labels = mixedMoment B raw36677step0 raw36677step0Labels := by
      have hz : ∀ j, raw36677 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36677step0 = (fun i j => raw36677 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36677step0 raw36677; decide +kernel
      have hl : raw36677step0Labels = raw36677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36677 raw36677Labels permutation520 hz
    mixedMoment B raw36677step0 raw36677step0Labels = mixedMoment B raw36677step1 raw36677step1Labels := by
      have ha : raw36677step1 = (fun i j => raw36677step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36677step1 raw36677step0; decide +kernel
      have hl : raw36677step1Labels = raw36677step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36677step0 raw36677step0Labels permutation56 permutation2
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw36678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36678 raw36678Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw36678 raw36678Labels = mixedMoment B raw36678step0 raw36678step0Labels := by
      have ha : raw36678step0 = (fun i j => raw36678 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36678step0 raw36678; decide +kernel
      have hl : raw36678step0Labels = raw36678Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36678 raw36678Labels permutation268 permutation2
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw36679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36679step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36679 raw36679Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw36679 raw36679Labels = mixedMoment B raw36679step0 raw36679step0Labels := by
      have hz : ∀ j, raw36679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36679step0 = (fun i j => raw36679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36679step0 raw36679; decide +kernel
      have hl : raw36679step0Labels = raw36679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36679 raw36679Labels permutation346 hz
    mixedMoment B raw36679step0 raw36679step0Labels = mixedMoment B raw36679step1 raw36679step1Labels := by
      have ha : raw36679step1 = (fun i j => raw36679step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36679step1 raw36679step0; decide +kernel
      have hl : raw36679step1Labels = raw36679step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36679step0 raw36679step0Labels permutation34 permutation3
    mixedMoment B raw36679step1 raw36679step1Labels = mixedMoment B raw36679step2 raw36679step2Labels := by
      have ha : raw36679step2 = raw36679step1 := by apply Matrix.ext; unfold raw36679step2 raw36679step1; decide +kernel
      have hl : raw36679step1Labels = labelEmbedding6 ∘ raw36679step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36679step1 raw36679step1Labels raw36679step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw36680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36680 raw36680Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw36680 raw36680Labels = mixedMoment B raw36680step0 raw36680step0Labels := by
      have hz : ∀ j, raw36680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36680step0 = (fun i j => raw36680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36680step0 raw36680; decide +kernel
      have hl : raw36680step0Labels = raw36680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36680 raw36680Labels permutation346 hz
    mixedMoment B raw36680step0 raw36680step0Labels = mixedMoment B raw36680step1 raw36680step1Labels := by
      have ha : raw36680step1 = (fun i j => raw36680step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36680step1 raw36680step0; decide +kernel
      have hl : raw36680step1Labels = raw36680step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36680step0 raw36680step0Labels permutation59 permutation2
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw36681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36681 raw36681Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw36681 raw36681Labels = mixedMoment B raw36681step0 raw36681step0Labels := by
      have ha : raw36681step0 = (fun i j => raw36681 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36681step0 raw36681; decide +kernel
      have hl : raw36681step0Labels = raw36681Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36681 raw36681Labels permutation268 permutation2
    _ = mixedMoment B node5335 node5335Labels := by rfl

def raw36682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw36682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw36682step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36682 raw36682Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw36682 raw36682Labels = mixedMoment B raw36682step0 raw36682step0Labels := by
      have hz : ∀ j, raw36682 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36682step0 = (fun i j => raw36682 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36682step0 raw36682; decide +kernel
      have hl : raw36682step0Labels = raw36682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36682 raw36682Labels permutation520 hz
    mixedMoment B raw36682step0 raw36682step0Labels = mixedMoment B raw36682step1 raw36682step1Labels := by
      have hz : ∀ j, raw36682step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36682step1 = (fun i j => raw36682step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36682step1 raw36682step0; decide +kernel
      have hl : raw36682step1Labels = raw36682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36682step0 raw36682step0Labels permutation80 hz
    mixedMoment B raw36682step1 raw36682step1Labels = mixedMoment B raw36682step2 raw36682step2Labels := by
      have ha : raw36682step2 = (fun i j => raw36682step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36682step2 raw36682step1; decide +kernel
      have hl : raw36682step2Labels = raw36682step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36682step1 raw36682step1Labels permutation15 permutation2
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw36683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36683 raw36683Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw36683 raw36683Labels = mixedMoment B raw36683step0 raw36683step0Labels := by
      have hz : ∀ j, raw36683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36683step0 = (fun i j => raw36683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36683step0 raw36683; decide +kernel
      have hl : raw36683step0Labels = raw36683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36683 raw36683Labels permutation346 hz
    mixedMoment B raw36683step0 raw36683step0Labels = mixedMoment B raw36683step1 raw36683step1Labels := by
      have ha : raw36683step1 = (fun i j => raw36683step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36683step1 raw36683step0; decide +kernel
      have hl : raw36683step1Labels = raw36683step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36683step0 raw36683step0Labels permutation59 permutation2
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw36684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36684step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36684 raw36684Labels = mixedMoment B node4966 node4966Labels := by
  calc
    mixedMoment B raw36684 raw36684Labels = mixedMoment B raw36684step0 raw36684step0Labels := by
      have hz : ∀ j, raw36684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36684step0 = (fun i j => raw36684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36684step0 raw36684; decide +kernel
      have hl : raw36684step0Labels = raw36684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36684 raw36684Labels permutation346 hz
    mixedMoment B raw36684step0 raw36684step0Labels = mixedMoment B raw36684step1 raw36684step1Labels := by
      have ha : raw36684step1 = (fun i j => raw36684step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36684step1 raw36684step0; decide +kernel
      have hl : raw36684step1Labels = raw36684step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36684step0 raw36684step0Labels permutation33 permutation3
    mixedMoment B raw36684step1 raw36684step1Labels = mixedMoment B raw36684step2 raw36684step2Labels := by
      have ha : raw36684step2 = raw36684step1 := by apply Matrix.ext; unfold raw36684step2 raw36684step1; decide +kernel
      have hl : raw36684step1Labels = labelEmbedding6 ∘ raw36684step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36684step1 raw36684step1Labels raw36684step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4966 node4966Labels := by rfl

def raw36685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36685 raw36685Labels = mixedMoment B node4951 node4951Labels := by
  calc
    mixedMoment B raw36685 raw36685Labels = mixedMoment B raw36685step0 raw36685step0Labels := by
      have hz : ∀ j, raw36685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36685step0 = (fun i j => raw36685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36685step0 raw36685; decide +kernel
      have hl : raw36685step0Labels = raw36685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36685 raw36685Labels permutation346 hz
    mixedMoment B raw36685step0 raw36685step0Labels = mixedMoment B raw36685step1 raw36685step1Labels := by
      have ha : raw36685step1 = (fun i j => raw36685step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36685step1 raw36685step0; decide +kernel
      have hl : raw36685step1Labels = raw36685step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36685step0 raw36685step0Labels permutation56 permutation2
    _ = mixedMoment B node4951 node4951Labels := by rfl

def raw36686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36686 raw36686Labels = mixedMoment B node5338 node5338Labels := by
  calc
    mixedMoment B raw36686 raw36686Labels = mixedMoment B raw36686step0 raw36686step0Labels := by
      have ha : raw36686step0 = (fun i j => raw36686 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36686step0 raw36686; decide +kernel
      have hl : raw36686step0Labels = raw36686Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36686 raw36686Labels permutation265 permutation2
    _ = mixedMoment B node5338 node5338Labels := by rfl

def raw36687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36687step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36687 raw36687Labels = mixedMoment B node5361 node5361Labels := by
  calc
    mixedMoment B raw36687 raw36687Labels = mixedMoment B raw36687step0 raw36687step0Labels := by
      have hz : ∀ j, raw36687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36687step0 = (fun i j => raw36687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36687step0 raw36687; decide +kernel
      have hl : raw36687step0Labels = raw36687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36687 raw36687Labels permutation346 hz
    mixedMoment B raw36687step0 raw36687step0Labels = mixedMoment B raw36687step1 raw36687step1Labels := by
      have ha : raw36687step1 = (fun i j => raw36687step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36687step1 raw36687step0; decide +kernel
      have hl : raw36687step1Labels = raw36687step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36687step0 raw36687step0Labels permutation56 permutation2
    _ = mixedMoment B node5361 node5361Labels := by rfl

def raw36688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw36688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw36688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36688 raw36688Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw36688 raw36688Labels = mixedMoment B raw36688step0 raw36688step0Labels := by
      have hz : ∀ j, raw36688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36688step0 = (fun i j => raw36688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36688step0 raw36688; decide +kernel
      have hl : raw36688step0Labels = raw36688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36688 raw36688Labels permutation346 hz
    mixedMoment B raw36688step0 raw36688step0Labels = mixedMoment B raw36688step1 raw36688step1Labels := by
      have ha : raw36688step1 = (fun i j => raw36688step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36688step1 raw36688step0; decide +kernel
      have hl : raw36688step1Labels = raw36688step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36688step0 raw36688step0Labels permutation60 permutation2
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw36689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw36689step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw36689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36689 raw36689Labels = mixedMoment B node4965 node4965Labels := by
  calc
    mixedMoment B raw36689 raw36689Labels = mixedMoment B raw36689step0 raw36689step0Labels := by
      have hz : ∀ j, raw36689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36689step0 = (fun i j => raw36689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36689step0 raw36689; decide +kernel
      have hl : raw36689step0Labels = raw36689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36689 raw36689Labels permutation346 hz
    mixedMoment B raw36689step0 raw36689step0Labels = mixedMoment B raw36689step1 raw36689step1Labels := by
      have ha : raw36689step1 = (fun i j => raw36689step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36689step1 raw36689step0; decide +kernel
      have hl : raw36689step1Labels = raw36689step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36689step0 raw36689step0Labels permutation32 permutation3
    mixedMoment B raw36689step1 raw36689step1Labels = mixedMoment B raw36689step2 raw36689step2Labels := by
      have ha : raw36689step2 = raw36689step1 := by apply Matrix.ext; unfold raw36689step2 raw36689step1; decide +kernel
      have hl : raw36689step1Labels = labelEmbedding6 ∘ raw36689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36689step1 raw36689step1Labels raw36689step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4965 node4965Labels := by rfl

def raw36690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw36690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36690 raw36690Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw36690 raw36690Labels = mixedMoment B raw36690step0 raw36690step0Labels := by
      have hz : ∀ j, raw36690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36690step0 = (fun i j => raw36690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36690step0 raw36690; decide +kernel
      have hl : raw36690step0Labels = raw36690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36690 raw36690Labels permutation346 hz
    mixedMoment B raw36690step0 raw36690step0Labels = mixedMoment B raw36690step1 raw36690step1Labels := by
      have ha : raw36690step1 = (fun i j => raw36690step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36690step1 raw36690step0; decide +kernel
      have hl : raw36690step1Labels = raw36690step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36690step0 raw36690step0Labels permutation58 permutation2
    _ = mixedMoment B node4944 node4944Labels := by rfl

def raw36691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36691step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36691step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36691step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36691 raw36691Labels = mixedMoment B node5044 node5044Labels := by
  calc
    mixedMoment B raw36691 raw36691Labels = mixedMoment B raw36691step0 raw36691step0Labels := by
      have ha : raw36691step0 = (fun i j => raw36691 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36691step0 raw36691; decide +kernel
      have hl : raw36691step0Labels = raw36691Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36691 raw36691Labels permutation688 permutation3
    mixedMoment B raw36691step0 raw36691step0Labels = mixedMoment B raw36691step1 raw36691step1Labels := by
      have ha : raw36691step1 = -raw36691step0 := by apply Matrix.ext; change ∀ i j, raw36691step1 i j = -(raw36691step0 i j); unfold raw36691step1 raw36691step0; decide +kernel
      have hl : raw36691step1Labels = raw36691step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36691step1 raw36691step1Labels = mixedMoment B raw36691step2 raw36691step2Labels := by
      have ha : raw36691step2 = raw36691step1 := by apply Matrix.ext; unfold raw36691step2 raw36691step1; decide +kernel
      have hl : raw36691step1Labels = labelEmbedding6 ∘ raw36691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36691step1 raw36691step1Labels raw36691step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5044 node5044Labels := by rfl

def raw36692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36692step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36692step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36692step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36692step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36692 raw36692Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw36692 raw36692Labels = mixedMoment B raw36692step0 raw36692step0Labels := by
      have hz : ∀ j, raw36692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36692step0 = (fun i j => raw36692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36692step0 raw36692; decide +kernel
      have hl : raw36692step0Labels = raw36692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36692 raw36692Labels permutation346 hz
    mixedMoment B raw36692step0 raw36692step0Labels = mixedMoment B raw36692step1 raw36692step1Labels := by
      have ha : raw36692step1 = (fun i j => raw36692step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36692step1 raw36692step0; decide +kernel
      have hl : raw36692step1Labels = raw36692step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36692step0 raw36692step0Labels permutation151 permutation3
    mixedMoment B raw36692step1 raw36692step1Labels = mixedMoment B raw36692step2 raw36692step2Labels := by
      have ha : raw36692step2 = -raw36692step1 := by apply Matrix.ext; change ∀ i j, raw36692step2 i j = -(raw36692step1 i j); unfold raw36692step2 raw36692step1; decide +kernel
      have hl : raw36692step2Labels = raw36692step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36692step2 raw36692step2Labels = mixedMoment B raw36692step3 raw36692step3Labels := by
      have ha : raw36692step3 = raw36692step2 := by apply Matrix.ext; unfold raw36692step3 raw36692step2; decide +kernel
      have hl : raw36692step2Labels = labelEmbedding6 ∘ raw36692step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36692step2 raw36692step2Labels raw36692step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw36693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw36693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw36693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![3, -2, -1]]
def raw36693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36693step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36693step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36693step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36693step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36693 raw36693Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw36693 raw36693Labels = mixedMoment B raw36693step0 raw36693step0Labels := by
      have hz : ∀ j, raw36693 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36693step0 = (fun i j => raw36693 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36693step0 raw36693; decide +kernel
      have hl : raw36693step0Labels = raw36693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36693 raw36693Labels permutation520 hz
    mixedMoment B raw36693step0 raw36693step0Labels = mixedMoment B raw36693step1 raw36693step1Labels := by
      have hz : ∀ j, raw36693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36693step1 = (fun i j => raw36693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36693step1 raw36693step0; decide +kernel
      have hl : raw36693step1Labels = raw36693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36693step0 raw36693step0Labels permutation80 hz
    mixedMoment B raw36693step1 raw36693step1Labels = mixedMoment B raw36693step2 raw36693step2Labels := by
      have ha : raw36693step2 = (fun i j => raw36693step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36693step2 raw36693step1; decide +kernel
      have hl : raw36693step2Labels = raw36693step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36693step1 raw36693step1Labels permutation31 permutation3
    mixedMoment B raw36693step2 raw36693step2Labels = mixedMoment B raw36693step3 raw36693step3Labels := by
      have ha : raw36693step3 = -raw36693step2 := by apply Matrix.ext; change ∀ i j, raw36693step3 i j = -(raw36693step2 i j); unfold raw36693step3 raw36693step2; decide +kernel
      have hl : raw36693step3Labels = raw36693step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36693step3 raw36693step3Labels = mixedMoment B raw36693step4 raw36693step4Labels := by
      have ha : raw36693step4 = raw36693step3 := by apply Matrix.ext; unfold raw36693step4 raw36693step3; decide +kernel
      have hl : raw36693step3Labels = labelEmbedding6 ∘ raw36693step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36693step3 raw36693step3Labels raw36693step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw36694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36694Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36694step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36694step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36694step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36694step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36694step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36694 raw36694Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw36694 raw36694Labels = mixedMoment B raw36694step0 raw36694step0Labels := by
      have hz : ∀ j, raw36694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36694step0 = (fun i j => raw36694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36694step0 raw36694; decide +kernel
      have hl : raw36694step0Labels = raw36694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36694 raw36694Labels permutation346 hz
    mixedMoment B raw36694step0 raw36694step0Labels = mixedMoment B raw36694step1 raw36694step1Labels := by
      have ha : raw36694step1 = (fun i j => raw36694step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36694step1 raw36694step0; decide +kernel
      have hl : raw36694step1Labels = raw36694step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36694step0 raw36694step0Labels permutation59 permutation7
    mixedMoment B raw36694step1 raw36694step1Labels = mixedMoment B raw36694step2 raw36694step2Labels := by
      have ha : raw36694step2 = -raw36694step1 := by apply Matrix.ext; change ∀ i j, raw36694step2 i j = -(raw36694step1 i j); unfold raw36694step2 raw36694step1; decide +kernel
      have hl : raw36694step2Labels = raw36694step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36694step2 raw36694step2Labels = mixedMoment B raw36694step3 raw36694step3Labels := by
      have ha : raw36694step3 = raw36694step2 := by apply Matrix.ext; unfold raw36694step3 raw36694step2; decide +kernel
      have hl : raw36694step2Labels = labelEmbedding1 ∘ raw36694step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36694step2 raw36694step2Labels raw36694step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

def raw36695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36695Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36695step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36695step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36695step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36695step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36695 raw36695Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw36695 raw36695Labels = mixedMoment B raw36695step0 raw36695step0Labels := by
      have ha : raw36695step0 = (fun i j => raw36695 (permutation268 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36695step0 raw36695; decide +kernel
      have hl : raw36695step0Labels = raw36695Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36695 raw36695Labels permutation268 permutation7
    mixedMoment B raw36695step0 raw36695step0Labels = mixedMoment B raw36695step1 raw36695step1Labels := by
      have ha : raw36695step1 = -raw36695step0 := by apply Matrix.ext; change ∀ i j, raw36695step1 i j = -(raw36695step0 i j); unfold raw36695step1 raw36695step0; decide +kernel
      have hl : raw36695step1Labels = raw36695step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36695step1 raw36695step1Labels = mixedMoment B raw36695step2 raw36695step2Labels := by
      have ha : raw36695step2 = raw36695step1 := by apply Matrix.ext; unfold raw36695step2 raw36695step1; decide +kernel
      have hl : raw36695step1Labels = labelEmbedding1 ∘ raw36695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36695step1 raw36695step1Labels raw36695step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

def raw36696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36696Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36696step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36696step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36696step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36696step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36696step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36696 raw36696Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw36696 raw36696Labels = mixedMoment B raw36696step0 raw36696step0Labels := by
      have hz : ∀ j, raw36696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36696step0 = (fun i j => raw36696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36696step0 raw36696; decide +kernel
      have hl : raw36696step0Labels = raw36696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36696 raw36696Labels permutation346 hz
    mixedMoment B raw36696step0 raw36696step0Labels = mixedMoment B raw36696step1 raw36696step1Labels := by
      have ha : raw36696step1 = (fun i j => raw36696step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36696step1 raw36696step0; decide +kernel
      have hl : raw36696step1Labels = raw36696step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36696step0 raw36696step0Labels permutation59 permutation7
    mixedMoment B raw36696step1 raw36696step1Labels = mixedMoment B raw36696step2 raw36696step2Labels := by
      have ha : raw36696step2 = -raw36696step1 := by apply Matrix.ext; change ∀ i j, raw36696step2 i j = -(raw36696step1 i j); unfold raw36696step2 raw36696step1; decide +kernel
      have hl : raw36696step2Labels = raw36696step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36696step2 raw36696step2Labels = mixedMoment B raw36696step3 raw36696step3Labels := by
      have ha : raw36696step3 = raw36696step2 := by apply Matrix.ext; unfold raw36696step3 raw36696step2; decide +kernel
      have hl : raw36696step2Labels = labelEmbedding1 ∘ raw36696step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36696step2 raw36696step2Labels raw36696step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw36697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36697Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36697step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1]]
def raw36697step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36697step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36697step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36697step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36697step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36697step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36697 raw36697Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw36697 raw36697Labels = mixedMoment B raw36697step0 raw36697step0Labels := by
      have hz : ∀ j, raw36697 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36697step0 = (fun i j => raw36697 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36697step0 raw36697; decide +kernel
      have hl : raw36697step0Labels = raw36697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36697 raw36697Labels permutation520 hz
    mixedMoment B raw36697step0 raw36697step0Labels = mixedMoment B raw36697step1 raw36697step1Labels := by
      have hz : ∀ j, raw36697step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36697step1 = (fun i j => raw36697step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36697step1 raw36697step0; decide +kernel
      have hl : raw36697step1Labels = raw36697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36697step0 raw36697step0Labels permutation80 hz
    mixedMoment B raw36697step1 raw36697step1Labels = mixedMoment B raw36697step2 raw36697step2Labels := by
      have ha : raw36697step2 = (fun i j => raw36697step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36697step2 raw36697step1; decide +kernel
      have hl : raw36697step2Labels = raw36697step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36697step1 raw36697step1Labels permutation15 permutation7
    mixedMoment B raw36697step2 raw36697step2Labels = mixedMoment B raw36697step3 raw36697step3Labels := by
      have ha : raw36697step3 = -raw36697step2 := by apply Matrix.ext; change ∀ i j, raw36697step3 i j = -(raw36697step2 i j); unfold raw36697step3 raw36697step2; decide +kernel
      have hl : raw36697step3Labels = raw36697step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36697step3 raw36697step3Labels = mixedMoment B raw36697step4 raw36697step4Labels := by
      have ha : raw36697step4 = raw36697step3 := by apply Matrix.ext; unfold raw36697step4 raw36697step3; decide +kernel
      have hl : raw36697step3Labels = labelEmbedding1 ∘ raw36697step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36697step3 raw36697step3Labels raw36697step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw36698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36698Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36698step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36698step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36698step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36698step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36698step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36698 raw36698Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw36698 raw36698Labels = mixedMoment B raw36698step0 raw36698step0Labels := by
      have hz : ∀ j, raw36698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36698step0 = (fun i j => raw36698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36698step0 raw36698; decide +kernel
      have hl : raw36698step0Labels = raw36698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36698 raw36698Labels permutation346 hz
    mixedMoment B raw36698step0 raw36698step0Labels = mixedMoment B raw36698step1 raw36698step1Labels := by
      have ha : raw36698step1 = (fun i j => raw36698step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36698step1 raw36698step0; decide +kernel
      have hl : raw36698step1Labels = raw36698step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36698step0 raw36698step0Labels permutation59 permutation7
    mixedMoment B raw36698step1 raw36698step1Labels = mixedMoment B raw36698step2 raw36698step2Labels := by
      have ha : raw36698step2 = -raw36698step1 := by apply Matrix.ext; change ∀ i j, raw36698step2 i j = -(raw36698step1 i j); unfold raw36698step2 raw36698step1; decide +kernel
      have hl : raw36698step2Labels = raw36698step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36698step2 raw36698step2Labels = mixedMoment B raw36698step3 raw36698step3Labels := by
      have ha : raw36698step3 = raw36698step2 := by apply Matrix.ext; unfold raw36698step3 raw36698step2; decide +kernel
      have hl : raw36698step2Labels = labelEmbedding1 ∘ raw36698step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36698step2 raw36698step2Labels raw36698step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw36699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36699step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36699step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36699step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36699step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36699step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36699 raw36699Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw36699 raw36699Labels = mixedMoment B raw36699step0 raw36699step0Labels := by
      have hz : ∀ j, raw36699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36699step0 = (fun i j => raw36699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36699step0 raw36699; decide +kernel
      have hl : raw36699step0Labels = raw36699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36699 raw36699Labels permutation346 hz
    mixedMoment B raw36699step0 raw36699step0Labels = mixedMoment B raw36699step1 raw36699step1Labels := by
      have ha : raw36699step1 = (fun i j => raw36699step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36699step1 raw36699step0; decide +kernel
      have hl : raw36699step1Labels = raw36699step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36699step0 raw36699step0Labels permutation38 permutation5
    mixedMoment B raw36699step1 raw36699step1Labels = mixedMoment B raw36699step2 raw36699step2Labels := by
      have ha : raw36699step2 = -raw36699step1 := by apply Matrix.ext; change ∀ i j, raw36699step2 i j = -(raw36699step1 i j); unfold raw36699step2 raw36699step1; decide +kernel
      have hl : raw36699step2Labels = raw36699step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36699step2 raw36699step2Labels = mixedMoment B raw36699step3 raw36699step3Labels := by
      have ha : raw36699step3 = raw36699step2 := by apply Matrix.ext; unfold raw36699step3 raw36699step2; decide +kernel
      have hl : raw36699step2Labels = labelEmbedding1 ∘ raw36699step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36699step2 raw36699step2Labels raw36699step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw36700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36700step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36700 raw36700Labels = mixedMoment B node3950 node3950Labels := by
  calc
    mixedMoment B raw36700 raw36700Labels = mixedMoment B raw36700step0 raw36700step0Labels := by
      have ha : raw36700step0 = (fun i j => raw36700 (permutation518 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36700step0 raw36700; decide +kernel
      have hl : raw36700step0Labels = raw36700Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36700 raw36700Labels permutation518 permutation7
    mixedMoment B raw36700step0 raw36700step0Labels = mixedMoment B raw36700step1 raw36700step1Labels := by
      have ha : raw36700step1 = raw36700step0 := by apply Matrix.ext; unfold raw36700step1 raw36700step0; decide +kernel
      have hl : raw36700step0Labels = labelEmbedding1 ∘ raw36700step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36700step0 raw36700step0Labels raw36700step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3950 node3950Labels := by rfl

def raw36701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36701step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36701step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36701step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36701step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36701 raw36701Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw36701 raw36701Labels = mixedMoment B raw36701step0 raw36701step0Labels := by
      have hz : ∀ j, raw36701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36701step0 = (fun i j => raw36701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36701step0 raw36701; decide +kernel
      have hl : raw36701step0Labels = raw36701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36701 raw36701Labels permutation346 hz
    mixedMoment B raw36701step0 raw36701step0Labels = mixedMoment B raw36701step1 raw36701step1Labels := by
      have ha : raw36701step1 = (fun i j => raw36701step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36701step1 raw36701step0; decide +kernel
      have hl : raw36701step1Labels = raw36701step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36701step0 raw36701step0Labels permutation59 permutation7
    mixedMoment B raw36701step1 raw36701step1Labels = mixedMoment B raw36701step2 raw36701step2Labels := by
      have ha : raw36701step2 = -raw36701step1 := by apply Matrix.ext; change ∀ i j, raw36701step2 i j = -(raw36701step1 i j); unfold raw36701step2 raw36701step1; decide +kernel
      have hl : raw36701step2Labels = raw36701step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36701step2 raw36701step2Labels = mixedMoment B raw36701step3 raw36701step3Labels := by
      have ha : raw36701step3 = raw36701step2 := by apply Matrix.ext; unfold raw36701step3 raw36701step2; decide +kernel
      have hl : raw36701step2Labels = labelEmbedding1 ∘ raw36701step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36701step2 raw36701step2Labels raw36701step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw36702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw36702step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw36702step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36702step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw36702step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36702 raw36702Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw36702 raw36702Labels = mixedMoment B raw36702step0 raw36702step0Labels := by
      have hz : ∀ j, raw36702 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36702step0 = (fun i j => raw36702 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36702step0 raw36702; decide +kernel
      have hl : raw36702step0Labels = raw36702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36702 raw36702Labels permutation520 hz
    mixedMoment B raw36702step0 raw36702step0Labels = mixedMoment B raw36702step1 raw36702step1Labels := by
      have hz : ∀ j, raw36702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36702step1 = (fun i j => raw36702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36702step1 raw36702step0; decide +kernel
      have hl : raw36702step1Labels = raw36702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36702step0 raw36702step0Labels permutation80 hz
    mixedMoment B raw36702step1 raw36702step1Labels = mixedMoment B raw36702step2 raw36702step2Labels := by
      have ha : raw36702step2 = (fun i j => raw36702step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36702step2 raw36702step1; decide +kernel
      have hl : raw36702step2Labels = raw36702step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36702step1 raw36702step1Labels permutation24 permutation7
    mixedMoment B raw36702step2 raw36702step2Labels = mixedMoment B raw36702step3 raw36702step3Labels := by
      have ha : raw36702step3 = raw36702step2 := by apply Matrix.ext; unfold raw36702step3 raw36702step2; decide +kernel
      have hl : raw36702step2Labels = labelEmbedding1 ∘ raw36702step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36702step2 raw36702step2Labels raw36702step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw36703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36703step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36703step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36703 raw36703Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw36703 raw36703Labels = mixedMoment B raw36703step0 raw36703step0Labels := by
      have hz : ∀ j, raw36703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36703step0 = (fun i j => raw36703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36703step0 raw36703; decide +kernel
      have hl : raw36703step0Labels = raw36703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36703 raw36703Labels permutation346 hz
    mixedMoment B raw36703step0 raw36703step0Labels = mixedMoment B raw36703step1 raw36703step1Labels := by
      have ha : raw36703step1 = (fun i j => raw36703step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36703step1 raw36703step0; decide +kernel
      have hl : raw36703step1Labels = raw36703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36703step0 raw36703step0Labels permutation59 permutation7
    mixedMoment B raw36703step1 raw36703step1Labels = mixedMoment B raw36703step2 raw36703step2Labels := by
      have ha : raw36703step2 = -raw36703step1 := by apply Matrix.ext; change ∀ i j, raw36703step2 i j = -(raw36703step1 i j); unfold raw36703step2 raw36703step1; decide +kernel
      have hl : raw36703step2Labels = raw36703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36703step2 raw36703step2Labels = mixedMoment B raw36703step3 raw36703step3Labels := by
      have ha : raw36703step3 = raw36703step2 := by apply Matrix.ext; unfold raw36703step3 raw36703step2; decide +kernel
      have hl : raw36703step2Labels = labelEmbedding1 ∘ raw36703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36703step2 raw36703step2Labels raw36703step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw36704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36704step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36704 raw36704Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw36704 raw36704Labels = mixedMoment B raw36704step0 raw36704step0Labels := by
      have ha : raw36704step0 = (fun i j => raw36704 (permutation200 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36704step0 raw36704; decide +kernel
      have hl : raw36704step0Labels = raw36704Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36704 raw36704Labels permutation200 permutation5
    mixedMoment B raw36704step0 raw36704step0Labels = mixedMoment B raw36704step1 raw36704step1Labels := by
      have ha : raw36704step1 = -raw36704step0 := by apply Matrix.ext; change ∀ i j, raw36704step1 i j = -(raw36704step0 i j); unfold raw36704step1 raw36704step0; decide +kernel
      have hl : raw36704step1Labels = raw36704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36704step1 raw36704step1Labels = mixedMoment B raw36704step2 raw36704step2Labels := by
      have ha : raw36704step2 = raw36704step1 := by apply Matrix.ext; unfold raw36704step2 raw36704step1; decide +kernel
      have hl : raw36704step1Labels = labelEmbedding1 ∘ raw36704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36704step1 raw36704step1Labels raw36704step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

def raw36705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36705step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36705step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36705 raw36705Labels = mixedMoment B node3405 node3405Labels := by
  calc
    mixedMoment B raw36705 raw36705Labels = mixedMoment B raw36705step0 raw36705step0Labels := by
      have ha : raw36705step0 = (fun i j => raw36705 (permutation268 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36705step0 raw36705; decide +kernel
      have hl : raw36705step0Labels = raw36705Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36705 raw36705Labels permutation268 permutation7
    mixedMoment B raw36705step0 raw36705step0Labels = mixedMoment B raw36705step1 raw36705step1Labels := by
      have ha : raw36705step1 = -raw36705step0 := by apply Matrix.ext; change ∀ i j, raw36705step1 i j = -(raw36705step0 i j); unfold raw36705step1 raw36705step0; decide +kernel
      have hl : raw36705step1Labels = raw36705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36705step1 raw36705step1Labels = mixedMoment B raw36705step2 raw36705step2Labels := by
      have ha : raw36705step2 = raw36705step1 := by apply Matrix.ext; unfold raw36705step2 raw36705step1; decide +kernel
      have hl : raw36705step1Labels = labelEmbedding1 ∘ raw36705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36705step1 raw36705step1Labels raw36705step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3405 node3405Labels := by rfl

def raw36706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36706step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36706step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36706step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36706 raw36706Labels = mixedMoment B node3759 node3759Labels := by
  calc
    mixedMoment B raw36706 raw36706Labels = mixedMoment B raw36706step0 raw36706step0Labels := by
      have ha : raw36706step0 = (fun i j => raw36706 (permutation268 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36706step0 raw36706; decide +kernel
      have hl : raw36706step0Labels = raw36706Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36706 raw36706Labels permutation268 permutation7
    mixedMoment B raw36706step0 raw36706step0Labels = mixedMoment B raw36706step1 raw36706step1Labels := by
      have ha : raw36706step1 = -raw36706step0 := by apply Matrix.ext; change ∀ i j, raw36706step1 i j = -(raw36706step0 i j); unfold raw36706step1 raw36706step0; decide +kernel
      have hl : raw36706step1Labels = raw36706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36706step1 raw36706step1Labels = mixedMoment B raw36706step2 raw36706step2Labels := by
      have ha : raw36706step2 = raw36706step1 := by apply Matrix.ext; unfold raw36706step2 raw36706step1; decide +kernel
      have hl : raw36706step1Labels = labelEmbedding1 ∘ raw36706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36706step1 raw36706step1Labels raw36706step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3759 node3759Labels := by rfl

def raw36707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36707 raw36707Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw36707 raw36707Labels = mixedMoment B raw36707step0 raw36707step0Labels := by
      have hz : ∀ j, raw36707 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36707step0 = (fun i j => raw36707 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36707step0 raw36707; decide +kernel
      have hl : raw36707step0Labels = raw36707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36707 raw36707Labels permutation520 hz
    mixedMoment B raw36707step0 raw36707step0Labels = mixedMoment B raw36707step1 raw36707step1Labels := by
      have ha : raw36707step1 = (fun i j => raw36707step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36707step1 raw36707step0; decide +kernel
      have hl : raw36707step1Labels = raw36707step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36707step0 raw36707step0Labels permutation57 permutation7
    mixedMoment B raw36707step1 raw36707step1Labels = mixedMoment B raw36707step2 raw36707step2Labels := by
      have ha : raw36707step2 = -raw36707step1 := by apply Matrix.ext; change ∀ i j, raw36707step2 i j = -(raw36707step1 i j); unfold raw36707step2 raw36707step1; decide +kernel
      have hl : raw36707step2Labels = raw36707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36707step2 raw36707step2Labels = mixedMoment B raw36707step3 raw36707step3Labels := by
      have ha : raw36707step3 = raw36707step2 := by apply Matrix.ext; unfold raw36707step3 raw36707step2; decide +kernel
      have hl : raw36707step2Labels = labelEmbedding1 ∘ raw36707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36707step2 raw36707step2Labels raw36707step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

def raw36708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36708step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36708step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36708step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36708 raw36708Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw36708 raw36708Labels = mixedMoment B raw36708step0 raw36708step0Labels := by
      have ha : raw36708step0 = (fun i j => raw36708 (permutation268 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36708step0 raw36708; decide +kernel
      have hl : raw36708step0Labels = raw36708Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36708 raw36708Labels permutation268 permutation7
    mixedMoment B raw36708step0 raw36708step0Labels = mixedMoment B raw36708step1 raw36708step1Labels := by
      have ha : raw36708step1 = -raw36708step0 := by apply Matrix.ext; change ∀ i j, raw36708step1 i j = -(raw36708step0 i j); unfold raw36708step1 raw36708step0; decide +kernel
      have hl : raw36708step1Labels = raw36708step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36708step1 raw36708step1Labels = mixedMoment B raw36708step2 raw36708step2Labels := by
      have ha : raw36708step2 = raw36708step1 := by apply Matrix.ext; unfold raw36708step2 raw36708step1; decide +kernel
      have hl : raw36708step1Labels = labelEmbedding1 ∘ raw36708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36708step1 raw36708step1Labels raw36708step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

def raw36709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw36709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw36709step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36709step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw36709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36709 raw36709Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw36709 raw36709Labels = mixedMoment B raw36709step0 raw36709step0Labels := by
      have hz : ∀ j, raw36709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36709step0 = (fun i j => raw36709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36709step0 raw36709; decide +kernel
      have hl : raw36709step0Labels = raw36709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36709 raw36709Labels permutation346 hz
    mixedMoment B raw36709step0 raw36709step0Labels = mixedMoment B raw36709step1 raw36709step1Labels := by
      have ha : raw36709step1 = (fun i j => raw36709step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36709step1 raw36709step0; decide +kernel
      have hl : raw36709step1Labels = raw36709step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36709step0 raw36709step0Labels permutation32 permutation5
    mixedMoment B raw36709step1 raw36709step1Labels = mixedMoment B raw36709step2 raw36709step2Labels := by
      have ha : raw36709step2 = -raw36709step1 := by apply Matrix.ext; change ∀ i j, raw36709step2 i j = -(raw36709step1 i j); unfold raw36709step2 raw36709step1; decide +kernel
      have hl : raw36709step2Labels = raw36709step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36709step2 raw36709step2Labels = mixedMoment B raw36709step3 raw36709step3Labels := by
      have ha : raw36709step3 = raw36709step2 := by apply Matrix.ext; unfold raw36709step3 raw36709step2; decide +kernel
      have hl : raw36709step2Labels = labelEmbedding1 ∘ raw36709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36709step2 raw36709step2Labels raw36709step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

def raw36710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36710 raw36710Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw36710 raw36710Labels = mixedMoment B raw36710step0 raw36710step0Labels := by
      have hz : ∀ j, raw36710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36710step0 = (fun i j => raw36710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36710step0 raw36710; decide +kernel
      have hl : raw36710step0Labels = raw36710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36710 raw36710Labels permutation346 hz
    mixedMoment B raw36710step0 raw36710step0Labels = mixedMoment B raw36710step1 raw36710step1Labels := by
      have ha : raw36710step1 = (fun i j => raw36710step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36710step1 raw36710step0; decide +kernel
      have hl : raw36710step1Labels = raw36710step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36710step0 raw36710step0Labels permutation59 permutation7
    mixedMoment B raw36710step1 raw36710step1Labels = mixedMoment B raw36710step2 raw36710step2Labels := by
      have ha : raw36710step2 = -raw36710step1 := by apply Matrix.ext; change ∀ i j, raw36710step2 i j = -(raw36710step1 i j); unfold raw36710step2 raw36710step1; decide +kernel
      have hl : raw36710step2Labels = raw36710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36710step2 raw36710step2Labels = mixedMoment B raw36710step3 raw36710step3Labels := by
      have ha : raw36710step3 = raw36710step2 := by apply Matrix.ext; unfold raw36710step3 raw36710step2; decide +kernel
      have hl : raw36710step2Labels = labelEmbedding1 ∘ raw36710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36710step2 raw36710step2Labels raw36710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

def raw36711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36711step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36711 raw36711Labels = mixedMoment B node3753 node3753Labels := by
  calc
    mixedMoment B raw36711 raw36711Labels = mixedMoment B raw36711step0 raw36711step0Labels := by
      have ha : raw36711step0 = (fun i j => raw36711 (permutation518 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36711step0 raw36711; decide +kernel
      have hl : raw36711step0Labels = raw36711Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36711 raw36711Labels permutation518 permutation7
    mixedMoment B raw36711step0 raw36711step0Labels = mixedMoment B raw36711step1 raw36711step1Labels := by
      have ha : raw36711step1 = raw36711step0 := by apply Matrix.ext; unfold raw36711step1 raw36711step0; decide +kernel
      have hl : raw36711step0Labels = labelEmbedding1 ∘ raw36711step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36711step0 raw36711step0Labels raw36711step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3753 node3753Labels := by rfl

def raw36712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw36712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw36712step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36712 raw36712Labels = mixedMoment B node3775 node3775Labels := by
  calc
    mixedMoment B raw36712 raw36712Labels = mixedMoment B raw36712step0 raw36712step0Labels := by
      have hz : ∀ j, raw36712 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36712step0 = (fun i j => raw36712 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36712step0 raw36712; decide +kernel
      have hl : raw36712step0Labels = raw36712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36712 raw36712Labels permutation520 hz
    mixedMoment B raw36712step0 raw36712step0Labels = mixedMoment B raw36712step1 raw36712step1Labels := by
      have hz : ∀ j, raw36712step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36712step1 = (fun i j => raw36712step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36712step1 raw36712step0; decide +kernel
      have hl : raw36712step1Labels = raw36712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36712step0 raw36712step0Labels permutation80 hz
    mixedMoment B raw36712step1 raw36712step1Labels = mixedMoment B raw36712step2 raw36712step2Labels := by
      have ha : raw36712step2 = (fun i j => raw36712step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36712step2 raw36712step1; decide +kernel
      have hl : raw36712step2Labels = raw36712step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36712step1 raw36712step1Labels permutation24 permutation7
    mixedMoment B raw36712step2 raw36712step2Labels = mixedMoment B raw36712step3 raw36712step3Labels := by
      have ha : raw36712step3 = raw36712step2 := by apply Matrix.ext; unfold raw36712step3 raw36712step2; decide +kernel
      have hl : raw36712step2Labels = labelEmbedding1 ∘ raw36712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36712step2 raw36712step2Labels raw36712step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3775 node3775Labels := by rfl

def raw36713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36713step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36713step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36713 raw36713Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw36713 raw36713Labels = mixedMoment B raw36713step0 raw36713step0Labels := by
      have hz : ∀ j, raw36713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36713step0 = (fun i j => raw36713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36713step0 raw36713; decide +kernel
      have hl : raw36713step0Labels = raw36713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36713 raw36713Labels permutation346 hz
    mixedMoment B raw36713step0 raw36713step0Labels = mixedMoment B raw36713step1 raw36713step1Labels := by
      have ha : raw36713step1 = (fun i j => raw36713step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36713step1 raw36713step0; decide +kernel
      have hl : raw36713step1Labels = raw36713step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36713step0 raw36713step0Labels permutation59 permutation7
    mixedMoment B raw36713step1 raw36713step1Labels = mixedMoment B raw36713step2 raw36713step2Labels := by
      have ha : raw36713step2 = -raw36713step1 := by apply Matrix.ext; change ∀ i j, raw36713step2 i j = -(raw36713step1 i j); unfold raw36713step2 raw36713step1; decide +kernel
      have hl : raw36713step2Labels = raw36713step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36713step2 raw36713step2Labels = mixedMoment B raw36713step3 raw36713step3Labels := by
      have ha : raw36713step3 = raw36713step2 := by apply Matrix.ext; unfold raw36713step3 raw36713step2; decide +kernel
      have hl : raw36713step2Labels = labelEmbedding1 ∘ raw36713step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36713step2 raw36713step2Labels raw36713step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw36714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw36714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36714 raw36714Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw36714 raw36714Labels = mixedMoment B raw36714step0 raw36714step0Labels := by
      have hz : ∀ j, raw36714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36714step0 = (fun i j => raw36714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36714step0 raw36714; decide +kernel
      have hl : raw36714step0Labels = raw36714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36714 raw36714Labels permutation346 hz
    mixedMoment B raw36714step0 raw36714step0Labels = mixedMoment B raw36714step1 raw36714step1Labels := by
      have ha : raw36714step1 = (fun i j => raw36714step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36714step1 raw36714step0; decide +kernel
      have hl : raw36714step1Labels = raw36714step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36714step0 raw36714step0Labels permutation39 permutation5
    mixedMoment B raw36714step1 raw36714step1Labels = mixedMoment B raw36714step2 raw36714step2Labels := by
      have ha : raw36714step2 = -raw36714step1 := by apply Matrix.ext; change ∀ i j, raw36714step2 i j = -(raw36714step1 i j); unfold raw36714step2 raw36714step1; decide +kernel
      have hl : raw36714step2Labels = raw36714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36714step2 raw36714step2Labels = mixedMoment B raw36714step3 raw36714step3Labels := by
      have ha : raw36714step3 = raw36714step2 := by apply Matrix.ext; unfold raw36714step3 raw36714step2; decide +kernel
      have hl : raw36714step2Labels = labelEmbedding1 ∘ raw36714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36714step2 raw36714step2Labels raw36714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

def raw36715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw36715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36715step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36715 raw36715Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw36715 raw36715Labels = mixedMoment B raw36715step0 raw36715step0Labels := by
      have hz : ∀ j, raw36715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36715step0 = (fun i j => raw36715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36715step0 raw36715; decide +kernel
      have hl : raw36715step0Labels = raw36715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36715 raw36715Labels permutation346 hz
    mixedMoment B raw36715step0 raw36715step0Labels = mixedMoment B raw36715step1 raw36715step1Labels := by
      have ha : raw36715step1 = (fun i j => raw36715step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36715step1 raw36715step0; decide +kernel
      have hl : raw36715step1Labels = raw36715step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36715step0 raw36715step0Labels permutation59 permutation7
    mixedMoment B raw36715step1 raw36715step1Labels = mixedMoment B raw36715step2 raw36715step2Labels := by
      have ha : raw36715step2 = -raw36715step1 := by apply Matrix.ext; change ∀ i j, raw36715step2 i j = -(raw36715step1 i j); unfold raw36715step2 raw36715step1; decide +kernel
      have hl : raw36715step2Labels = raw36715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36715step2 raw36715step2Labels = mixedMoment B raw36715step3 raw36715step3Labels := by
      have ha : raw36715step3 = raw36715step2 := by apply Matrix.ext; unfold raw36715step3 raw36715step2; decide +kernel
      have hl : raw36715step2Labels = labelEmbedding1 ∘ raw36715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36715step2 raw36715step2Labels raw36715step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

def raw36716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw36716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36716 raw36716Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw36716 raw36716Labels = mixedMoment B raw36716step0 raw36716step0Labels := by
      have ha : raw36716step0 = (fun i j => raw36716 (permutation268 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36716step0 raw36716; decide +kernel
      have hl : raw36716step0Labels = raw36716Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36716 raw36716Labels permutation268 permutation7
    mixedMoment B raw36716step0 raw36716step0Labels = mixedMoment B raw36716step1 raw36716step1Labels := by
      have ha : raw36716step1 = -raw36716step0 := by apply Matrix.ext; change ∀ i j, raw36716step1 i j = -(raw36716step0 i j); unfold raw36716step1 raw36716step0; decide +kernel
      have hl : raw36716step1Labels = raw36716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36716step1 raw36716step1Labels = mixedMoment B raw36716step2 raw36716step2Labels := by
      have ha : raw36716step2 = raw36716step1 := by apply Matrix.ext; unfold raw36716step2 raw36716step1; decide +kernel
      have hl : raw36716step1Labels = labelEmbedding1 ∘ raw36716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36716step1 raw36716step1Labels raw36716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

def raw36717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36717 raw36717Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw36717 raw36717Labels = mixedMoment B raw36717step0 raw36717step0Labels := by
      have hz : ∀ j, raw36717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36717step0 = (fun i j => raw36717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36717step0 raw36717; decide +kernel
      have hl : raw36717step0Labels = raw36717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36717 raw36717Labels permutation346 hz
    mixedMoment B raw36717step0 raw36717step0Labels = mixedMoment B raw36717step1 raw36717step1Labels := by
      have ha : raw36717step1 = (fun i j => raw36717step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36717step1 raw36717step0; decide +kernel
      have hl : raw36717step1Labels = raw36717step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36717step0 raw36717step0Labels permutation124 permutation5
    mixedMoment B raw36717step1 raw36717step1Labels = mixedMoment B raw36717step2 raw36717step2Labels := by
      have ha : raw36717step2 = raw36717step1 := by apply Matrix.ext; unfold raw36717step2 raw36717step1; decide +kernel
      have hl : raw36717step1Labels = labelEmbedding1 ∘ raw36717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36717step1 raw36717step1Labels raw36717step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3772 node3772Labels := by rfl

def raw36718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw36718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw36718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36718 raw36718Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw36718 raw36718Labels = mixedMoment B raw36718step0 raw36718step0Labels := by
      have hz : ∀ j, raw36718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36718step0 = (fun i j => raw36718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36718step0 raw36718; decide +kernel
      have hl : raw36718step0Labels = raw36718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36718 raw36718Labels permutation346 hz
    mixedMoment B raw36718step0 raw36718step0Labels = mixedMoment B raw36718step1 raw36718step1Labels := by
      have ha : raw36718step1 = (fun i j => raw36718step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36718step1 raw36718step0; decide +kernel
      have hl : raw36718step1Labels = raw36718step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36718step0 raw36718step0Labels permutation59 permutation7
    mixedMoment B raw36718step1 raw36718step1Labels = mixedMoment B raw36718step2 raw36718step2Labels := by
      have ha : raw36718step2 = -raw36718step1 := by apply Matrix.ext; change ∀ i j, raw36718step2 i j = -(raw36718step1 i j); unfold raw36718step2 raw36718step1; decide +kernel
      have hl : raw36718step2Labels = raw36718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36718step2 raw36718step2Labels = mixedMoment B raw36718step3 raw36718step3Labels := by
      have ha : raw36718step3 = raw36718step2 := by apply Matrix.ext; unfold raw36718step3 raw36718step2; decide +kernel
      have hl : raw36718step2Labels = labelEmbedding1 ∘ raw36718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36718step2 raw36718step2Labels raw36718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

def raw36719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw36719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw36719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36719 raw36719Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw36719 raw36719Labels = mixedMoment B raw36719step0 raw36719step0Labels := by
      have hz : ∀ j, raw36719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36719step0 = (fun i j => raw36719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36719step0 raw36719; decide +kernel
      have hl : raw36719step0Labels = raw36719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36719 raw36719Labels permutation346 hz
    mixedMoment B raw36719step0 raw36719step0Labels = mixedMoment B raw36719step1 raw36719step1Labels := by
      have ha : raw36719step1 = (fun i j => raw36719step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36719step1 raw36719step0; decide +kernel
      have hl : raw36719step1Labels = raw36719step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36719step0 raw36719step0Labels permutation149 permutation5
    mixedMoment B raw36719step1 raw36719step1Labels = mixedMoment B raw36719step2 raw36719step2Labels := by
      have ha : raw36719step2 = raw36719step1 := by apply Matrix.ext; unfold raw36719step2 raw36719step1; decide +kernel
      have hl : raw36719step1Labels = labelEmbedding1 ∘ raw36719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36719step1 raw36719step1Labels raw36719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

def raw36720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw36720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw36720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw36720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36720 raw36720Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw36720 raw36720Labels = mixedMoment B raw36720step0 raw36720step0Labels := by
      have hz : ∀ j, raw36720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36720step0 = (fun i j => raw36720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36720step0 raw36720; decide +kernel
      have hl : raw36720step0Labels = raw36720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36720 raw36720Labels permutation346 hz
    mixedMoment B raw36720step0 raw36720step0Labels = mixedMoment B raw36720step1 raw36720step1Labels := by
      have ha : raw36720step1 = (fun i j => raw36720step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36720step1 raw36720step0; decide +kernel
      have hl : raw36720step1Labels = raw36720step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36720step0 raw36720step0Labels permutation59 permutation7
    mixedMoment B raw36720step1 raw36720step1Labels = mixedMoment B raw36720step2 raw36720step2Labels := by
      have ha : raw36720step2 = -raw36720step1 := by apply Matrix.ext; change ∀ i j, raw36720step2 i j = -(raw36720step1 i j); unfold raw36720step2 raw36720step1; decide +kernel
      have hl : raw36720step2Labels = raw36720step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36720step2 raw36720step2Labels = mixedMoment B raw36720step3 raw36720step3Labels := by
      have ha : raw36720step3 = raw36720step2 := by apply Matrix.ext; unfold raw36720step3 raw36720step2; decide +kernel
      have hl : raw36720step2Labels = labelEmbedding1 ∘ raw36720step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36720step2 raw36720step2Labels raw36720step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

def raw36721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36721 raw36721Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw36721 raw36721Labels = mixedMoment B raw36721step0 raw36721step0Labels := by
      have ha : raw36721step0 = (fun i j => raw36721 (permutation676 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36721step0 raw36721; decide +kernel
      have hl : raw36721step0Labels = raw36721Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36721 raw36721Labels permutation676 permutation5
    mixedMoment B raw36721step0 raw36721step0Labels = mixedMoment B raw36721step1 raw36721step1Labels := by
      have ha : raw36721step1 = raw36721step0 := by apply Matrix.ext; unfold raw36721step1 raw36721step0; decide +kernel
      have hl : raw36721step0Labels = labelEmbedding1 ∘ raw36721step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36721step0 raw36721step0Labels raw36721step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

def raw36722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36722 raw36722Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw36722 raw36722Labels = mixedMoment B raw36722step0 raw36722step0Labels := by
      have hz : ∀ j, raw36722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36722step0 = (fun i j => raw36722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36722step0 raw36722; decide +kernel
      have hl : raw36722step0Labels = raw36722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36722 raw36722Labels permutation346 hz
    mixedMoment B raw36722step0 raw36722step0Labels = mixedMoment B raw36722step1 raw36722step1Labels := by
      have ha : raw36722step1 = (fun i j => raw36722step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36722step1 raw36722step0; decide +kernel
      have hl : raw36722step1Labels = raw36722step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36722step0 raw36722step0Labels permutation148 permutation5
    mixedMoment B raw36722step1 raw36722step1Labels = mixedMoment B raw36722step2 raw36722step2Labels := by
      have ha : raw36722step2 = raw36722step1 := by apply Matrix.ext; unfold raw36722step2 raw36722step1; decide +kernel
      have hl : raw36722step1Labels = labelEmbedding1 ∘ raw36722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36722step1 raw36722step1Labels raw36722step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw36723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw36723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw36723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![3, -2, -1]]
def raw36723step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw36723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36723step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw36723step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36723 raw36723Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw36723 raw36723Labels = mixedMoment B raw36723step0 raw36723step0Labels := by
      have hz : ∀ j, raw36723 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36723step0 = (fun i j => raw36723 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36723step0 raw36723; decide +kernel
      have hl : raw36723step0Labels = raw36723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36723 raw36723Labels permutation520 hz
    mixedMoment B raw36723step0 raw36723step0Labels = mixedMoment B raw36723step1 raw36723step1Labels := by
      have hz : ∀ j, raw36723step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36723step1 = (fun i j => raw36723step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36723step1 raw36723step0; decide +kernel
      have hl : raw36723step1Labels = raw36723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36723step0 raw36723step0Labels permutation80 hz
    mixedMoment B raw36723step1 raw36723step1Labels = mixedMoment B raw36723step2 raw36723step2Labels := by
      have ha : raw36723step2 = (fun i j => raw36723step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36723step2 raw36723step1; decide +kernel
      have hl : raw36723step2Labels = raw36723step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36723step1 raw36723step1Labels permutation29 permutation5
    mixedMoment B raw36723step2 raw36723step2Labels = mixedMoment B raw36723step3 raw36723step3Labels := by
      have ha : raw36723step3 = raw36723step2 := by apply Matrix.ext; unfold raw36723step3 raw36723step2; decide +kernel
      have hl : raw36723step2Labels = labelEmbedding1 ∘ raw36723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36723step2 raw36723step2Labels raw36723step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

def raw36724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 3, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36724step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36724 raw36724Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw36724 raw36724Labels = mixedMoment B raw36724step0 raw36724step0Labels := by
      have hz : ∀ j, raw36724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36724step0 = (fun i j => raw36724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36724step0 raw36724; decide +kernel
      have hl : raw36724step0Labels = raw36724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36724 raw36724Labels permutation346 hz
    mixedMoment B raw36724step0 raw36724step0Labels = mixedMoment B raw36724step1 raw36724step1Labels := by
      have ha : raw36724step1 = (fun i j => raw36724step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36724step1 raw36724step0; decide +kernel
      have hl : raw36724step1Labels = raw36724step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36724step0 raw36724step0Labels permutation58 permutation3
    mixedMoment B raw36724step1 raw36724step1Labels = mixedMoment B raw36724step2 raw36724step2Labels := by
      have ha : raw36724step2 = raw36724step1 := by apply Matrix.ext; unfold raw36724step2 raw36724step1; decide +kernel
      have hl : raw36724step1Labels = labelEmbedding6 ∘ raw36724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36724step1 raw36724step1Labels raw36724step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw36725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36725step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36725 raw36725Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw36725 raw36725Labels = mixedMoment B raw36725step0 raw36725step0Labels := by
      have ha : raw36725step0 = (fun i j => raw36725 (permutation291 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36725step0 raw36725; decide +kernel
      have hl : raw36725step0Labels = raw36725Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36725 raw36725Labels permutation291 permutation3
    mixedMoment B raw36725step0 raw36725step0Labels = mixedMoment B raw36725step1 raw36725step1Labels := by
      have ha : raw36725step1 = raw36725step0 := by apply Matrix.ext; unfold raw36725step1 raw36725step0; decide +kernel
      have hl : raw36725step0Labels = labelEmbedding6 ∘ raw36725step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36725step0 raw36725step0Labels raw36725step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw36726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36726step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36726 raw36726Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw36726 raw36726Labels = mixedMoment B raw36726step0 raw36726step0Labels := by
      have hz : ∀ j, raw36726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36726step0 = (fun i j => raw36726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36726step0 raw36726; decide +kernel
      have hl : raw36726step0Labels = raw36726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36726 raw36726Labels permutation346 hz
    mixedMoment B raw36726step0 raw36726step0Labels = mixedMoment B raw36726step1 raw36726step1Labels := by
      have ha : raw36726step1 = (fun i j => raw36726step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36726step1 raw36726step0; decide +kernel
      have hl : raw36726step1Labels = raw36726step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36726step0 raw36726step0Labels permutation56 permutation3
    mixedMoment B raw36726step1 raw36726step1Labels = mixedMoment B raw36726step2 raw36726step2Labels := by
      have ha : raw36726step2 = raw36726step1 := by apply Matrix.ext; unfold raw36726step2 raw36726step1; decide +kernel
      have hl : raw36726step1Labels = labelEmbedding6 ∘ raw36726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36726step1 raw36726step1Labels raw36726step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw36727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw36727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw36727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36727step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36727step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36727 raw36727Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw36727 raw36727Labels = mixedMoment B raw36727step0 raw36727step0Labels := by
      have hz : ∀ j, raw36727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36727step0 = (fun i j => raw36727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36727step0 raw36727; decide +kernel
      have hl : raw36727step0Labels = raw36727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36727 raw36727Labels permutation346 hz
    mixedMoment B raw36727step0 raw36727step0Labels = mixedMoment B raw36727step1 raw36727step1Labels := by
      have ha : raw36727step1 = (fun i j => raw36727step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36727step1 raw36727step0; decide +kernel
      have hl : raw36727step1Labels = raw36727step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36727step0 raw36727step0Labels permutation58 permutation3
    mixedMoment B raw36727step1 raw36727step1Labels = mixedMoment B raw36727step2 raw36727step2Labels := by
      have ha : raw36727step2 = raw36727step1 := by apply Matrix.ext; unfold raw36727step2 raw36727step1; decide +kernel
      have hl : raw36727step1Labels = labelEmbedding6 ∘ raw36727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36727step1 raw36727step1Labels raw36727step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw36728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw36728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw36728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36728step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36728step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36728 raw36728Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw36728 raw36728Labels = mixedMoment B raw36728step0 raw36728step0Labels := by
      have hz : ∀ j, raw36728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36728step0 = (fun i j => raw36728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36728step0 raw36728; decide +kernel
      have hl : raw36728step0Labels = raw36728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36728 raw36728Labels permutation346 hz
    mixedMoment B raw36728step0 raw36728step0Labels = mixedMoment B raw36728step1 raw36728step1Labels := by
      have ha : raw36728step1 = (fun i j => raw36728step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36728step1 raw36728step0; decide +kernel
      have hl : raw36728step1Labels = raw36728step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36728step0 raw36728step0Labels permutation59 permutation3
    mixedMoment B raw36728step1 raw36728step1Labels = mixedMoment B raw36728step2 raw36728step2Labels := by
      have ha : raw36728step2 = raw36728step1 := by apply Matrix.ext; unfold raw36728step2 raw36728step1; decide +kernel
      have hl : raw36728step1Labels = labelEmbedding6 ∘ raw36728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36728step1 raw36728step1Labels raw36728step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw36729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36729step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36729step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36729step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36729 raw36729Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw36729 raw36729Labels = mixedMoment B raw36729step0 raw36729step0Labels := by
      have ha : raw36729step0 = (fun i j => raw36729 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36729step0 raw36729; decide +kernel
      have hl : raw36729step0Labels = raw36729Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36729 raw36729Labels permutation277 permutation3
    mixedMoment B raw36729step0 raw36729step0Labels = mixedMoment B raw36729step1 raw36729step1Labels := by
      have ha : raw36729step1 = raw36729step0 := by apply Matrix.ext; unfold raw36729step1 raw36729step0; decide +kernel
      have hl : raw36729step0Labels = labelEmbedding6 ∘ raw36729step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36729step0 raw36729step0Labels raw36729step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

def raw36730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36730step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36730step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36730 raw36730Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw36730 raw36730Labels = mixedMoment B raw36730step0 raw36730step0Labels := by
      have ha : raw36730step0 = (fun i j => raw36730 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36730step0 raw36730; decide +kernel
      have hl : raw36730step0Labels = raw36730Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36730 raw36730Labels permutation273 permutation3
    mixedMoment B raw36730step0 raw36730step0Labels = mixedMoment B raw36730step1 raw36730step1Labels := by
      have ha : raw36730step1 = raw36730step0 := by apply Matrix.ext; unfold raw36730step1 raw36730step0; decide +kernel
      have hl : raw36730step0Labels = labelEmbedding6 ∘ raw36730step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36730step0 raw36730step0Labels raw36730step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw36731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw36731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36731step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36731step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36731 raw36731Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw36731 raw36731Labels = mixedMoment B raw36731step0 raw36731step0Labels := by
      have ha : raw36731step0 = (fun i j => raw36731 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36731step0 raw36731; decide +kernel
      have hl : raw36731step0Labels = raw36731Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36731 raw36731Labels permutation277 permutation3
    mixedMoment B raw36731step0 raw36731step0Labels = mixedMoment B raw36731step1 raw36731step1Labels := by
      have ha : raw36731step1 = raw36731step0 := by apply Matrix.ext; unfold raw36731step1 raw36731step0; decide +kernel
      have hl : raw36731step0Labels = labelEmbedding6 ∘ raw36731step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36731step0 raw36731step0Labels raw36731step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw36732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw36732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36732step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36732step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36732step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36732 raw36732Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw36732 raw36732Labels = mixedMoment B raw36732step0 raw36732step0Labels := by
      have ha : raw36732step0 = (fun i j => raw36732 (permutation281 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36732step0 raw36732; decide +kernel
      have hl : raw36732step0Labels = raw36732Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36732 raw36732Labels permutation281 permutation3
    mixedMoment B raw36732step0 raw36732step0Labels = mixedMoment B raw36732step1 raw36732step1Labels := by
      have ha : raw36732step1 = raw36732step0 := by apply Matrix.ext; unfold raw36732step1 raw36732step0; decide +kernel
      have hl : raw36732step0Labels = labelEmbedding6 ∘ raw36732step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36732step0 raw36732step0Labels raw36732step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw36733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw36733step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw36733step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36733 raw36733Labels = mixedMoment B node4645 node4645Labels := by
  calc
    mixedMoment B raw36733 raw36733Labels = mixedMoment B raw36733step0 raw36733step0Labels := by
      have hz : ∀ j, raw36733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36733step0 = (fun i j => raw36733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36733step0 raw36733; decide +kernel
      have hl : raw36733step0Labels = raw36733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36733 raw36733Labels permutation346 hz
    mixedMoment B raw36733step0 raw36733step0Labels = mixedMoment B raw36733step1 raw36733step1Labels := by
      have ha : raw36733step1 = (fun i j => raw36733step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36733step1 raw36733step0; decide +kernel
      have hl : raw36733step1Labels = raw36733step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36733step0 raw36733step0Labels permutation59 permutation3
    mixedMoment B raw36733step1 raw36733step1Labels = mixedMoment B raw36733step2 raw36733step2Labels := by
      have ha : raw36733step2 = raw36733step1 := by apply Matrix.ext; unfold raw36733step2 raw36733step1; decide +kernel
      have hl : raw36733step1Labels = labelEmbedding6 ∘ raw36733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36733step1 raw36733step1Labels raw36733step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4645 node4645Labels := by rfl

def raw36734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36734step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36734 raw36734Labels = mixedMoment B node4990 node4990Labels := by
  calc
    mixedMoment B raw36734 raw36734Labels = mixedMoment B raw36734step0 raw36734step0Labels := by
      have ha : raw36734step0 = (fun i j => raw36734 (permutation518 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36734step0 raw36734; decide +kernel
      have hl : raw36734step0Labels = raw36734Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36734 raw36734Labels permutation518 permutation5
    mixedMoment B raw36734step0 raw36734step0Labels = mixedMoment B raw36734step1 raw36734step1Labels := by
      have ha : raw36734step1 = raw36734step0 := by apply Matrix.ext; unfold raw36734step1 raw36734step0; decide +kernel
      have hl : raw36734step0Labels = labelEmbedding8 ∘ raw36734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36734step0 raw36734step0Labels raw36734step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4990 node4990Labels := by rfl

def raw36735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw36735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw36735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36735step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36735step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36735 raw36735Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw36735 raw36735Labels = mixedMoment B raw36735step0 raw36735step0Labels := by
      have hz : ∀ j, raw36735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36735step0 = (fun i j => raw36735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36735step0 raw36735; decide +kernel
      have hl : raw36735step0Labels = raw36735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36735 raw36735Labels permutation346 hz
    mixedMoment B raw36735step0 raw36735step0Labels = mixedMoment B raw36735step1 raw36735step1Labels := by
      have ha : raw36735step1 = (fun i j => raw36735step0 (permutation102 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36735step1 raw36735step0; decide +kernel
      have hl : raw36735step1Labels = raw36735step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36735step0 raw36735step0Labels permutation102 permutation5
    mixedMoment B raw36735step1 raw36735step1Labels = mixedMoment B raw36735step2 raw36735step2Labels := by
      have ha : raw36735step2 = raw36735step1 := by apply Matrix.ext; unfold raw36735step2 raw36735step1; decide +kernel
      have hl : raw36735step1Labels = labelEmbedding8 ∘ raw36735step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36735step1 raw36735step1Labels raw36735step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
