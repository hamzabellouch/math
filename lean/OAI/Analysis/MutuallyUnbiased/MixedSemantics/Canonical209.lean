import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26752Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26752 raw26752Labels = mixedMoment B node578 node578Labels := by
  calc
    mixedMoment B raw26752 raw26752Labels = mixedMoment B raw26752step0 raw26752step0Labels := by
      have ha : raw26752step0 = (fun i j => raw26752 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26752step0 raw26752; decide +kernel
      have hl : raw26752step0Labels = raw26752Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26752 raw26752Labels permutation153 permutation3
    _ = mixedMoment B node578 node578Labels := by rfl

def raw26753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26753Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26753 raw26753Labels = mixedMoment B node1162 node1162Labels := by
  calc
    mixedMoment B raw26753 raw26753Labels = mixedMoment B raw26753step0 raw26753step0Labels := by
      have ha : raw26753step0 = (fun i j => raw26753 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26753step0 raw26753; decide +kernel
      have hl : raw26753step0Labels = raw26753Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26753 raw26753Labels permutation153 permutation3
    _ = mixedMoment B node1162 node1162Labels := by rfl

def raw26754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26754 raw26754Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw26754 raw26754Labels = mixedMoment B raw26754step0 raw26754step0Labels := by
      have ha : raw26754step0 = (fun i j => raw26754 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26754step0 raw26754; decide +kernel
      have hl : raw26754step0Labels = raw26754Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26754 raw26754Labels permutation177 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw26755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26755 raw26755Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw26755 raw26755Labels = mixedMoment B raw26755step0 raw26755step0Labels := by
      have ha : raw26755step0 = (fun i j => raw26755 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26755step0 raw26755; decide +kernel
      have hl : raw26755step0Labels = raw26755Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26755 raw26755Labels permutation201 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw26756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw26756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26756step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26756 raw26756Labels = mixedMoment B node1266 node1266Labels := by
  calc
    mixedMoment B raw26756 raw26756Labels = mixedMoment B raw26756step0 raw26756step0Labels := by
      have hz : ∀ j, raw26756 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26756step0 = (fun i j => raw26756 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26756step0 raw26756; decide +kernel
      have hl : raw26756step0Labels = raw26756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26756 raw26756Labels permutation590 hz
    mixedMoment B raw26756step0 raw26756step0Labels = mixedMoment B raw26756step1 raw26756step1Labels := by
      have ha : raw26756step1 = (fun i j => raw26756step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26756step1 raw26756step0; decide +kernel
      have hl : raw26756step1Labels = raw26756step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26756step0 raw26756step0Labels permutation32 permutation3
    _ = mixedMoment B node1266 node1266Labels := by rfl

def raw26757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26757 raw26757Labels = mixedMoment B node577 node577Labels := by
  calc
    mixedMoment B raw26757 raw26757Labels = mixedMoment B raw26757step0 raw26757step0Labels := by
      have ha : raw26757step0 = (fun i j => raw26757 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26757step0 raw26757; decide +kernel
      have hl : raw26757step0Labels = raw26757Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26757 raw26757Labels permutation152 permutation3
    _ = mixedMoment B node577 node577Labels := by rfl

def raw26758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26758 raw26758Labels = mixedMoment B node1161 node1161Labels := by
  calc
    mixedMoment B raw26758 raw26758Labels = mixedMoment B raw26758step0 raw26758step0Labels := by
      have ha : raw26758step0 = (fun i j => raw26758 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26758step0 raw26758; decide +kernel
      have hl : raw26758step0Labels = raw26758Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26758 raw26758Labels permutation152 permutation3
    _ = mixedMoment B node1161 node1161Labels := by rfl

def raw26759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw26759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26759 raw26759Labels = mixedMoment B node1212 node1212Labels := by
  calc
    mixedMoment B raw26759 raw26759Labels = mixedMoment B raw26759step0 raw26759step0Labels := by
      have ha : raw26759step0 = (fun i j => raw26759 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26759step0 raw26759; decide +kernel
      have hl : raw26759step0Labels = raw26759Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26759 raw26759Labels permutation224 permutation3
    _ = mixedMoment B node1212 node1212Labels := by rfl

def raw26760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26760step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26760step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26760 raw26760Labels = mixedMoment B node3469 node3469Labels := by
  calc
    mixedMoment B raw26760 raw26760Labels = mixedMoment B raw26760step0 raw26760step0Labels := by
      have ha : raw26760step0 = (fun i j => raw26760 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26760step0 raw26760; decide +kernel
      have hl : raw26760step0Labels = raw26760Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26760 raw26760Labels permutation170 permutation7
    mixedMoment B raw26760step0 raw26760step0Labels = mixedMoment B raw26760step1 raw26760step1Labels := by
      have ha : raw26760step1 = -raw26760step0 := by apply Matrix.ext; change ∀ i j, raw26760step1 i j = -(raw26760step0 i j); unfold raw26760step1 raw26760step0; decide +kernel
      have hl : raw26760step1Labels = raw26760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26760step1 raw26760step1Labels = mixedMoment B raw26760step2 raw26760step2Labels := by
      have ha : raw26760step2 = raw26760step1 := by apply Matrix.ext; unfold raw26760step2 raw26760step1; decide +kernel
      have hl : raw26760step1Labels = labelEmbedding1 ∘ raw26760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26760step1 raw26760step1Labels raw26760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3469 node3469Labels := by rfl

def raw26761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26761step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26761step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26761 raw26761Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw26761 raw26761Labels = mixedMoment B raw26761step0 raw26761step0Labels := by
      have ha : raw26761step0 = (fun i j => raw26761 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26761step0 raw26761; decide +kernel
      have hl : raw26761step0Labels = raw26761Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26761 raw26761Labels permutation174 permutation7
    mixedMoment B raw26761step0 raw26761step0Labels = mixedMoment B raw26761step1 raw26761step1Labels := by
      have ha : raw26761step1 = -raw26761step0 := by apply Matrix.ext; change ∀ i j, raw26761step1 i j = -(raw26761step0 i j); unfold raw26761step1 raw26761step0; decide +kernel
      have hl : raw26761step1Labels = raw26761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26761step1 raw26761step1Labels = mixedMoment B raw26761step2 raw26761step2Labels := by
      have ha : raw26761step2 = raw26761step1 := by apply Matrix.ext; unfold raw26761step2 raw26761step1; decide +kernel
      have hl : raw26761step1Labels = labelEmbedding1 ∘ raw26761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26761step1 raw26761step1Labels raw26761step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw26762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26762step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26762step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26762step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26762 raw26762Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw26762 raw26762Labels = mixedMoment B raw26762step0 raw26762step0Labels := by
      have hz : ∀ j, raw26762 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26762step0 = (fun i j => raw26762 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26762step0 raw26762; decide +kernel
      have hl : raw26762step0Labels = raw26762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26762 raw26762Labels permutation590 hz
    mixedMoment B raw26762step0 raw26762step0Labels = mixedMoment B raw26762step1 raw26762step1Labels := by
      have ha : raw26762step1 = (fun i j => raw26762step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26762step1 raw26762step0; decide +kernel
      have hl : raw26762step1Labels = raw26762step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26762step0 raw26762step0Labels permutation32 permutation7
    mixedMoment B raw26762step1 raw26762step1Labels = mixedMoment B raw26762step2 raw26762step2Labels := by
      have ha : raw26762step2 = -raw26762step1 := by apply Matrix.ext; change ∀ i j, raw26762step2 i j = -(raw26762step1 i j); unfold raw26762step2 raw26762step1; decide +kernel
      have hl : raw26762step2Labels = raw26762step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26762step2 raw26762step2Labels = mixedMoment B raw26762step3 raw26762step3Labels := by
      have ha : raw26762step3 = raw26762step2 := by apply Matrix.ext; unfold raw26762step3 raw26762step2; decide +kernel
      have hl : raw26762step2Labels = labelEmbedding1 ∘ raw26762step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26762step2 raw26762step2Labels raw26762step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

def raw26763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26763step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26763step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26763step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26763 raw26763Labels = mixedMoment B node1502 node1502Labels := by
  calc
    mixedMoment B raw26763 raw26763Labels = mixedMoment B raw26763step0 raw26763step0Labels := by
      have ha : raw26763step0 = (fun i j => raw26763 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26763step0 raw26763; decide +kernel
      have hl : raw26763step0Labels = raw26763Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26763 raw26763Labels permutation185 permutation5
    mixedMoment B raw26763step0 raw26763step0Labels = mixedMoment B raw26763step1 raw26763step1Labels := by
      have ha : raw26763step1 = -raw26763step0 := by apply Matrix.ext; change ∀ i j, raw26763step1 i j = -(raw26763step0 i j); unfold raw26763step1 raw26763step0; decide +kernel
      have hl : raw26763step1Labels = raw26763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26763step1 raw26763step1Labels = mixedMoment B raw26763step2 raw26763step2Labels := by
      have ha : raw26763step2 = raw26763step1 := by apply Matrix.ext; unfold raw26763step2 raw26763step1; decide +kernel
      have hl : raw26763step1Labels = labelEmbedding1 ∘ raw26763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26763step1 raw26763step1Labels raw26763step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1502 node1502Labels := by rfl

def raw26764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26764step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26764 raw26764Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26764 raw26764Labels = mixedMoment B raw26764step0 raw26764step0Labels := by
      have ha : raw26764step0 = (fun i j => raw26764 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26764step0 raw26764; decide +kernel
      have hl : raw26764step0Labels = raw26764Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26764 raw26764Labels permutation185 permutation5
    mixedMoment B raw26764step0 raw26764step0Labels = mixedMoment B raw26764step1 raw26764step1Labels := by
      have ha : raw26764step1 = -raw26764step0 := by apply Matrix.ext; change ∀ i j, raw26764step1 i j = -(raw26764step0 i j); unfold raw26764step1 raw26764step0; decide +kernel
      have hl : raw26764step1Labels = raw26764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26764step1 raw26764step1Labels = mixedMoment B raw26764step2 raw26764step2Labels := by
      have ha : raw26764step2 = raw26764step1 := by apply Matrix.ext; unfold raw26764step2 raw26764step1; decide +kernel
      have hl : raw26764step1Labels = labelEmbedding1 ∘ raw26764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26764step1 raw26764step1Labels raw26764step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw26765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26765step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26765step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26765step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26765 raw26765Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26765 raw26765Labels = mixedMoment B raw26765step0 raw26765step0Labels := by
      have ha : raw26765step0 = (fun i j => raw26765 (permutation209 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26765step0 raw26765; decide +kernel
      have hl : raw26765step0Labels = raw26765Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26765 raw26765Labels permutation209 permutation5
    mixedMoment B raw26765step0 raw26765step0Labels = mixedMoment B raw26765step1 raw26765step1Labels := by
      have ha : raw26765step1 = -raw26765step0 := by apply Matrix.ext; change ∀ i j, raw26765step1 i j = -(raw26765step0 i j); unfold raw26765step1 raw26765step0; decide +kernel
      have hl : raw26765step1Labels = raw26765step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26765step1 raw26765step1Labels = mixedMoment B raw26765step2 raw26765step2Labels := by
      have ha : raw26765step2 = raw26765step1 := by apply Matrix.ext; unfold raw26765step2 raw26765step1; decide +kernel
      have hl : raw26765step1Labels = labelEmbedding1 ∘ raw26765step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26765step1 raw26765step1Labels raw26765step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw26766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26766step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26766step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26766 raw26766Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26766 raw26766Labels = mixedMoment B raw26766step0 raw26766step0Labels := by
      have ha : raw26766step0 = (fun i j => raw26766 (permutation233 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26766step0 raw26766; decide +kernel
      have hl : raw26766step0Labels = raw26766Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26766 raw26766Labels permutation233 permutation5
    mixedMoment B raw26766step0 raw26766step0Labels = mixedMoment B raw26766step1 raw26766step1Labels := by
      have ha : raw26766step1 = -raw26766step0 := by apply Matrix.ext; change ∀ i j, raw26766step1 i j = -(raw26766step0 i j); unfold raw26766step1 raw26766step0; decide +kernel
      have hl : raw26766step1Labels = raw26766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26766step1 raw26766step1Labels = mixedMoment B raw26766step2 raw26766step2Labels := by
      have ha : raw26766step2 = raw26766step1 := by apply Matrix.ext; unfold raw26766step2 raw26766step1; decide +kernel
      have hl : raw26766step1Labels = labelEmbedding1 ∘ raw26766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26766step1 raw26766step1Labels raw26766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw26767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26767step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26767step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26767step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26767step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26767 raw26767Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw26767 raw26767Labels = mixedMoment B raw26767step0 raw26767step0Labels := by
      have hz : ∀ j, raw26767 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26767step0 = (fun i j => raw26767 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26767step0 raw26767; decide +kernel
      have hl : raw26767step0Labels = raw26767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26767 raw26767Labels permutation590 hz
    mixedMoment B raw26767step0 raw26767step0Labels = mixedMoment B raw26767step1 raw26767step1Labels := by
      have ha : raw26767step1 = (fun i j => raw26767step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26767step1 raw26767step0; decide +kernel
      have hl : raw26767step1Labels = raw26767step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26767step0 raw26767step0Labels permutation32 permutation7
    mixedMoment B raw26767step1 raw26767step1Labels = mixedMoment B raw26767step2 raw26767step2Labels := by
      have ha : raw26767step2 = -raw26767step1 := by apply Matrix.ext; change ∀ i j, raw26767step2 i j = -(raw26767step1 i j); unfold raw26767step2 raw26767step1; decide +kernel
      have hl : raw26767step2Labels = raw26767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26767step2 raw26767step2Labels = mixedMoment B raw26767step3 raw26767step3Labels := by
      have ha : raw26767step3 = raw26767step2 := by apply Matrix.ext; unfold raw26767step3 raw26767step2; decide +kernel
      have hl : raw26767step2Labels = labelEmbedding1 ∘ raw26767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26767step2 raw26767step2Labels raw26767step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3304 node3304Labels := by rfl

def raw26768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26768step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26768step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26768 raw26768Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw26768 raw26768Labels = mixedMoment B raw26768step0 raw26768step0Labels := by
      have ha : raw26768step0 = (fun i j => raw26768 (permutation213 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26768step0 raw26768; decide +kernel
      have hl : raw26768step0Labels = raw26768Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26768 raw26768Labels permutation213 permutation5
    mixedMoment B raw26768step0 raw26768step0Labels = mixedMoment B raw26768step1 raw26768step1Labels := by
      have ha : raw26768step1 = -raw26768step0 := by apply Matrix.ext; change ∀ i j, raw26768step1 i j = -(raw26768step0 i j); unfold raw26768step1 raw26768step0; decide +kernel
      have hl : raw26768step1Labels = raw26768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26768step1 raw26768step1Labels = mixedMoment B raw26768step2 raw26768step2Labels := by
      have ha : raw26768step2 = raw26768step1 := by apply Matrix.ext; unfold raw26768step2 raw26768step1; decide +kernel
      have hl : raw26768step1Labels = labelEmbedding1 ∘ raw26768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26768step1 raw26768step1Labels raw26768step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

def raw26769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26769step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26769step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26769step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26769 raw26769Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw26769 raw26769Labels = mixedMoment B raw26769step0 raw26769step0Labels := by
      have ha : raw26769step0 = (fun i j => raw26769 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26769step0 raw26769; decide +kernel
      have hl : raw26769step0Labels = raw26769Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26769 raw26769Labels permutation173 permutation7
    mixedMoment B raw26769step0 raw26769step0Labels = mixedMoment B raw26769step1 raw26769step1Labels := by
      have ha : raw26769step1 = -raw26769step0 := by apply Matrix.ext; change ∀ i j, raw26769step1 i j = -(raw26769step0 i j); unfold raw26769step1 raw26769step0; decide +kernel
      have hl : raw26769step1Labels = raw26769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26769step1 raw26769step1Labels = mixedMoment B raw26769step2 raw26769step2Labels := by
      have ha : raw26769step2 = raw26769step1 := by apply Matrix.ext; unfold raw26769step2 raw26769step1; decide +kernel
      have hl : raw26769step1Labels = labelEmbedding1 ∘ raw26769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26769step1 raw26769step1Labels raw26769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

def raw26770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26770step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26770step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26770 raw26770Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw26770 raw26770Labels = mixedMoment B raw26770step0 raw26770step0Labels := by
      have ha : raw26770step0 = (fun i j => raw26770 (permutation213 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26770step0 raw26770; decide +kernel
      have hl : raw26770step0Labels = raw26770Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26770 raw26770Labels permutation213 permutation5
    mixedMoment B raw26770step0 raw26770step0Labels = mixedMoment B raw26770step1 raw26770step1Labels := by
      have ha : raw26770step1 = -raw26770step0 := by apply Matrix.ext; change ∀ i j, raw26770step1 i j = -(raw26770step0 i j); unfold raw26770step1 raw26770step0; decide +kernel
      have hl : raw26770step1Labels = raw26770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26770step1 raw26770step1Labels = mixedMoment B raw26770step2 raw26770step2Labels := by
      have ha : raw26770step2 = raw26770step1 := by apply Matrix.ext; unfold raw26770step2 raw26770step1; decide +kernel
      have hl : raw26770step1Labels = labelEmbedding1 ∘ raw26770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26770step1 raw26770step1Labels raw26770step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw26771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26771step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26771step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26771step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26771step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26771 raw26771Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw26771 raw26771Labels = mixedMoment B raw26771step0 raw26771step0Labels := by
      have ha : raw26771step0 = (fun i j => raw26771 (permutation235 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26771step0 raw26771; decide +kernel
      have hl : raw26771step0Labels = raw26771Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26771 raw26771Labels permutation235 permutation5
    mixedMoment B raw26771step0 raw26771step0Labels = mixedMoment B raw26771step1 raw26771step1Labels := by
      have ha : raw26771step1 = -raw26771step0 := by apply Matrix.ext; change ∀ i j, raw26771step1 i j = -(raw26771step0 i j); unfold raw26771step1 raw26771step0; decide +kernel
      have hl : raw26771step1Labels = raw26771step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26771step1 raw26771step1Labels = mixedMoment B raw26771step2 raw26771step2Labels := by
      have ha : raw26771step2 = raw26771step1 := by apply Matrix.ext; unfold raw26771step2 raw26771step1; decide +kernel
      have hl : raw26771step1Labels = labelEmbedding1 ∘ raw26771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26771step1 raw26771step1Labels raw26771step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw26772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26772step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26772step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26772step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26772step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26772 raw26772Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw26772 raw26772Labels = mixedMoment B raw26772step0 raw26772step0Labels := by
      have hz : ∀ j, raw26772 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26772step0 = (fun i j => raw26772 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26772step0 raw26772; decide +kernel
      have hl : raw26772step0Labels = raw26772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26772 raw26772Labels permutation590 hz
    mixedMoment B raw26772step0 raw26772step0Labels = mixedMoment B raw26772step1 raw26772step1Labels := by
      have ha : raw26772step1 = (fun i j => raw26772step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26772step1 raw26772step0; decide +kernel
      have hl : raw26772step1Labels = raw26772step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26772step0 raw26772step0Labels permutation35 permutation7
    mixedMoment B raw26772step1 raw26772step1Labels = mixedMoment B raw26772step2 raw26772step2Labels := by
      have ha : raw26772step2 = -raw26772step1 := by apply Matrix.ext; change ∀ i j, raw26772step2 i j = -(raw26772step1 i j); unfold raw26772step2 raw26772step1; decide +kernel
      have hl : raw26772step2Labels = raw26772step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26772step2 raw26772step2Labels = mixedMoment B raw26772step3 raw26772step3Labels := by
      have ha : raw26772step3 = raw26772step2 := by apply Matrix.ext; unfold raw26772step3 raw26772step2; decide +kernel
      have hl : raw26772step2Labels = labelEmbedding1 ∘ raw26772step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26772step2 raw26772step2Labels raw26772step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw26773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26773step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26773step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26773step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26773 raw26773Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw26773 raw26773Labels = mixedMoment B raw26773step0 raw26773step0Labels := by
      have ha : raw26773step0 = (fun i j => raw26773 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26773step0 raw26773; decide +kernel
      have hl : raw26773step0Labels = raw26773Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26773 raw26773Labels permutation189 permutation5
    mixedMoment B raw26773step0 raw26773step0Labels = mixedMoment B raw26773step1 raw26773step1Labels := by
      have ha : raw26773step1 = -raw26773step0 := by apply Matrix.ext; change ∀ i j, raw26773step1 i j = -(raw26773step0 i j); unfold raw26773step1 raw26773step0; decide +kernel
      have hl : raw26773step1Labels = raw26773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26773step1 raw26773step1Labels = mixedMoment B raw26773step2 raw26773step2Labels := by
      have ha : raw26773step2 = raw26773step1 := by apply Matrix.ext; unfold raw26773step2 raw26773step1; decide +kernel
      have hl : raw26773step1Labels = labelEmbedding1 ∘ raw26773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26773step1 raw26773step1Labels raw26773step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

def raw26774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26774step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26774step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26774 raw26774Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw26774 raw26774Labels = mixedMoment B raw26774step0 raw26774step0Labels := by
      have ha : raw26774step0 = (fun i j => raw26774 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26774step0 raw26774; decide +kernel
      have hl : raw26774step0Labels = raw26774Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26774 raw26774Labels permutation171 permutation7
    mixedMoment B raw26774step0 raw26774step0Labels = mixedMoment B raw26774step1 raw26774step1Labels := by
      have ha : raw26774step1 = -raw26774step0 := by apply Matrix.ext; change ∀ i j, raw26774step1 i j = -(raw26774step0 i j); unfold raw26774step1 raw26774step0; decide +kernel
      have hl : raw26774step1Labels = raw26774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26774step1 raw26774step1Labels = mixedMoment B raw26774step2 raw26774step2Labels := by
      have ha : raw26774step2 = raw26774step1 := by apply Matrix.ext; unfold raw26774step2 raw26774step1; decide +kernel
      have hl : raw26774step1Labels = labelEmbedding1 ∘ raw26774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26774step1 raw26774step1Labels raw26774step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

def raw26775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26775step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26775step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26775 raw26775Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw26775 raw26775Labels = mixedMoment B raw26775step0 raw26775step0Labels := by
      have ha : raw26775step0 = (fun i j => raw26775 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26775step0 raw26775; decide +kernel
      have hl : raw26775step0Labels = raw26775Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26775 raw26775Labels permutation189 permutation5
    mixedMoment B raw26775step0 raw26775step0Labels = mixedMoment B raw26775step1 raw26775step1Labels := by
      have ha : raw26775step1 = -raw26775step0 := by apply Matrix.ext; change ∀ i j, raw26775step1 i j = -(raw26775step0 i j); unfold raw26775step1 raw26775step0; decide +kernel
      have hl : raw26775step1Labels = raw26775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26775step1 raw26775step1Labels = mixedMoment B raw26775step2 raw26775step2Labels := by
      have ha : raw26775step2 = raw26775step1 := by apply Matrix.ext; unfold raw26775step2 raw26775step1; decide +kernel
      have hl : raw26775step1Labels = labelEmbedding1 ∘ raw26775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26775step1 raw26775step1Labels raw26775step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw26776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26776step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26776step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26776step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26776step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26776 raw26776Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw26776 raw26776Labels = mixedMoment B raw26776step0 raw26776step0Labels := by
      have ha : raw26776step0 = (fun i j => raw26776 (permutation231 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26776step0 raw26776; decide +kernel
      have hl : raw26776step0Labels = raw26776Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26776 raw26776Labels permutation231 permutation5
    mixedMoment B raw26776step0 raw26776step0Labels = mixedMoment B raw26776step1 raw26776step1Labels := by
      have ha : raw26776step1 = -raw26776step0 := by apply Matrix.ext; change ∀ i j, raw26776step1 i j = -(raw26776step0 i j); unfold raw26776step1 raw26776step0; decide +kernel
      have hl : raw26776step1Labels = raw26776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26776step1 raw26776step1Labels = mixedMoment B raw26776step2 raw26776step2Labels := by
      have ha : raw26776step2 = raw26776step1 := by apply Matrix.ext; unfold raw26776step2 raw26776step1; decide +kernel
      have hl : raw26776step1Labels = labelEmbedding1 ∘ raw26776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26776step1 raw26776step1Labels raw26776step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw26777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26777step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26777step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26777step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26777step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26777step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26777 raw26777Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw26777 raw26777Labels = mixedMoment B raw26777step0 raw26777step0Labels := by
      have hz : ∀ j, raw26777 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26777step0 = (fun i j => raw26777 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26777step0 raw26777; decide +kernel
      have hl : raw26777step0Labels = raw26777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26777 raw26777Labels permutation590 hz
    mixedMoment B raw26777step0 raw26777step0Labels = mixedMoment B raw26777step1 raw26777step1Labels := by
      have ha : raw26777step1 = (fun i j => raw26777step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26777step1 raw26777step0; decide +kernel
      have hl : raw26777step1Labels = raw26777step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26777step0 raw26777step0Labels permutation33 permutation7
    mixedMoment B raw26777step1 raw26777step1Labels = mixedMoment B raw26777step2 raw26777step2Labels := by
      have ha : raw26777step2 = -raw26777step1 := by apply Matrix.ext; change ∀ i j, raw26777step2 i j = -(raw26777step1 i j); unfold raw26777step2 raw26777step1; decide +kernel
      have hl : raw26777step2Labels = raw26777step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26777step2 raw26777step2Labels = mixedMoment B raw26777step3 raw26777step3Labels := by
      have ha : raw26777step3 = raw26777step2 := by apply Matrix.ext; unfold raw26777step3 raw26777step2; decide +kernel
      have hl : raw26777step2Labels = labelEmbedding1 ∘ raw26777step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26777step2 raw26777step2Labels raw26777step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw26778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26778step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26778step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26778step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26778 raw26778Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw26778 raw26778Labels = mixedMoment B raw26778step0 raw26778step0Labels := by
      have ha : raw26778step0 = (fun i j => raw26778 (permutation183 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26778step0 raw26778; decide +kernel
      have hl : raw26778step0Labels = raw26778Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26778 raw26778Labels permutation183 permutation5
    mixedMoment B raw26778step0 raw26778step0Labels = mixedMoment B raw26778step1 raw26778step1Labels := by
      have ha : raw26778step1 = -raw26778step0 := by apply Matrix.ext; change ∀ i j, raw26778step1 i j = -(raw26778step0 i j); unfold raw26778step1 raw26778step0; decide +kernel
      have hl : raw26778step1Labels = raw26778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26778step1 raw26778step1Labels = mixedMoment B raw26778step2 raw26778step2Labels := by
      have ha : raw26778step2 = raw26778step1 := by apply Matrix.ext; unfold raw26778step2 raw26778step1; decide +kernel
      have hl : raw26778step1Labels = labelEmbedding1 ∘ raw26778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26778step1 raw26778step1Labels raw26778step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

def raw26779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26779step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26779step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26779step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26779 raw26779Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw26779 raw26779Labels = mixedMoment B raw26779step0 raw26779step0Labels := by
      have ha : raw26779step0 = (fun i j => raw26779 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26779step0 raw26779; decide +kernel
      have hl : raw26779step0Labels = raw26779Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26779 raw26779Labels permutation170 permutation7
    mixedMoment B raw26779step0 raw26779step0Labels = mixedMoment B raw26779step1 raw26779step1Labels := by
      have ha : raw26779step1 = -raw26779step0 := by apply Matrix.ext; change ∀ i j, raw26779step1 i j = -(raw26779step0 i j); unfold raw26779step1 raw26779step0; decide +kernel
      have hl : raw26779step1Labels = raw26779step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26779step1 raw26779step1Labels = mixedMoment B raw26779step2 raw26779step2Labels := by
      have ha : raw26779step2 = raw26779step1 := by apply Matrix.ext; unfold raw26779step2 raw26779step1; decide +kernel
      have hl : raw26779step1Labels = labelEmbedding1 ∘ raw26779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26779step1 raw26779step1Labels raw26779step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

def raw26780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26780step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26780step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26780step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26780step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26780 raw26780Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw26780 raw26780Labels = mixedMoment B raw26780step0 raw26780step0Labels := by
      have ha : raw26780step0 = (fun i j => raw26780 (permutation183 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26780step0 raw26780; decide +kernel
      have hl : raw26780step0Labels = raw26780Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26780 raw26780Labels permutation183 permutation5
    mixedMoment B raw26780step0 raw26780step0Labels = mixedMoment B raw26780step1 raw26780step1Labels := by
      have ha : raw26780step1 = -raw26780step0 := by apply Matrix.ext; change ∀ i j, raw26780step1 i j = -(raw26780step0 i j); unfold raw26780step1 raw26780step0; decide +kernel
      have hl : raw26780step1Labels = raw26780step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26780step1 raw26780step1Labels = mixedMoment B raw26780step2 raw26780step2Labels := by
      have ha : raw26780step2 = raw26780step1 := by apply Matrix.ext; unfold raw26780step2 raw26780step1; decide +kernel
      have hl : raw26780step1Labels = labelEmbedding1 ∘ raw26780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26780step1 raw26780step1Labels raw26780step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw26781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26781step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26781step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26781step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26781step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26781 raw26781Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw26781 raw26781Labels = mixedMoment B raw26781step0 raw26781step0Labels := by
      have ha : raw26781step0 = (fun i j => raw26781 (permutation207 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26781step0 raw26781; decide +kernel
      have hl : raw26781step0Labels = raw26781Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26781 raw26781Labels permutation207 permutation5
    mixedMoment B raw26781step0 raw26781step0Labels = mixedMoment B raw26781step1 raw26781step1Labels := by
      have ha : raw26781step1 = -raw26781step0 := by apply Matrix.ext; change ∀ i j, raw26781step1 i j = -(raw26781step0 i j); unfold raw26781step1 raw26781step0; decide +kernel
      have hl : raw26781step1Labels = raw26781step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26781step1 raw26781step1Labels = mixedMoment B raw26781step2 raw26781step2Labels := by
      have ha : raw26781step2 = raw26781step1 := by apply Matrix.ext; unfold raw26781step2 raw26781step1; decide +kernel
      have hl : raw26781step1Labels = labelEmbedding1 ∘ raw26781step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26781step1 raw26781step1Labels raw26781step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw26782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw26782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26782step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26782step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26782step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26782step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26782 raw26782Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw26782 raw26782Labels = mixedMoment B raw26782step0 raw26782step0Labels := by
      have hz : ∀ j, raw26782 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26782step0 = (fun i j => raw26782 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26782step0 raw26782; decide +kernel
      have hl : raw26782step0Labels = raw26782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26782 raw26782Labels permutation590 hz
    mixedMoment B raw26782step0 raw26782step0Labels = mixedMoment B raw26782step1 raw26782step1Labels := by
      have ha : raw26782step1 = (fun i j => raw26782step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26782step1 raw26782step0; decide +kernel
      have hl : raw26782step1Labels = raw26782step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26782step0 raw26782step0Labels permutation32 permutation7
    mixedMoment B raw26782step1 raw26782step1Labels = mixedMoment B raw26782step2 raw26782step2Labels := by
      have ha : raw26782step2 = -raw26782step1 := by apply Matrix.ext; change ∀ i j, raw26782step2 i j = -(raw26782step1 i j); unfold raw26782step2 raw26782step1; decide +kernel
      have hl : raw26782step2Labels = raw26782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26782step2 raw26782step2Labels = mixedMoment B raw26782step3 raw26782step3Labels := by
      have ha : raw26782step3 = raw26782step2 := by apply Matrix.ext; unfold raw26782step3 raw26782step2; decide +kernel
      have hl : raw26782step2Labels = labelEmbedding1 ∘ raw26782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26782step2 raw26782step2Labels raw26782step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw26783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw26783step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26783step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26783step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26783step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26783step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26783 raw26783Labels = mixedMoment B node1501 node1501Labels := by
  calc
    mixedMoment B raw26783 raw26783Labels = mixedMoment B raw26783step0 raw26783step0Labels := by
      have ha : raw26783step0 = (fun i j => raw26783 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26783step0 raw26783; decide +kernel
      have hl : raw26783step0Labels = raw26783Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26783 raw26783Labels permutation184 permutation5
    mixedMoment B raw26783step0 raw26783step0Labels = mixedMoment B raw26783step1 raw26783step1Labels := by
      have ha : raw26783step1 = -raw26783step0 := by apply Matrix.ext; change ∀ i j, raw26783step1 i j = -(raw26783step0 i j); unfold raw26783step1 raw26783step0; decide +kernel
      have hl : raw26783step1Labels = raw26783step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26783step1 raw26783step1Labels = mixedMoment B raw26783step2 raw26783step2Labels := by
      have ha : raw26783step2 = raw26783step1 := by apply Matrix.ext; unfold raw26783step2 raw26783step1; decide +kernel
      have hl : raw26783step1Labels = labelEmbedding1 ∘ raw26783step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26783step1 raw26783step1Labels raw26783step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1501 node1501Labels := by rfl

def raw26784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26784step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26784step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26784 raw26784Labels = mixedMoment B node3269 node3269Labels := by
  calc
    mixedMoment B raw26784 raw26784Labels = mixedMoment B raw26784step0 raw26784step0Labels := by
      have ha : raw26784step0 = (fun i j => raw26784 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26784step0 raw26784; decide +kernel
      have hl : raw26784step0Labels = raw26784Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26784 raw26784Labels permutation170 permutation7
    mixedMoment B raw26784step0 raw26784step0Labels = mixedMoment B raw26784step1 raw26784step1Labels := by
      have ha : raw26784step1 = -raw26784step0 := by apply Matrix.ext; change ∀ i j, raw26784step1 i j = -(raw26784step0 i j); unfold raw26784step1 raw26784step0; decide +kernel
      have hl : raw26784step1Labels = raw26784step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26784step1 raw26784step1Labels = mixedMoment B raw26784step2 raw26784step2Labels := by
      have ha : raw26784step2 = raw26784step1 := by apply Matrix.ext; unfold raw26784step2 raw26784step1; decide +kernel
      have hl : raw26784step1Labels = labelEmbedding1 ∘ raw26784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26784step1 raw26784step1Labels raw26784step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3269 node3269Labels := by rfl

def raw26785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw26785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw26785step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26785step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26785step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26785step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26785 raw26785Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw26785 raw26785Labels = mixedMoment B raw26785step0 raw26785step0Labels := by
      have ha : raw26785step0 = (fun i j => raw26785 (permutation232 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26785step0 raw26785; decide +kernel
      have hl : raw26785step0Labels = raw26785Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26785 raw26785Labels permutation232 permutation5
    mixedMoment B raw26785step0 raw26785step0Labels = mixedMoment B raw26785step1 raw26785step1Labels := by
      have ha : raw26785step1 = -raw26785step0 := by apply Matrix.ext; change ∀ i j, raw26785step1 i j = -(raw26785step0 i j); unfold raw26785step1 raw26785step0; decide +kernel
      have hl : raw26785step1Labels = raw26785step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26785step1 raw26785step1Labels = mixedMoment B raw26785step2 raw26785step2Labels := by
      have ha : raw26785step2 = raw26785step1 := by apply Matrix.ext; unfold raw26785step2 raw26785step1; decide +kernel
      have hl : raw26785step1Labels = labelEmbedding1 ∘ raw26785step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26785step1 raw26785step1Labels raw26785step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw26786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26786 raw26786Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw26786 raw26786Labels = mixedMoment B raw26786step0 raw26786step0Labels := by
      have ha : raw26786step0 = (fun i j => raw26786 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26786step0 raw26786; decide +kernel
      have hl : raw26786step0Labels = raw26786Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26786 raw26786Labels permutation170 permutation2
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw26787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26787 raw26787Labels = mixedMoment B node637 node637Labels := by
  calc
    mixedMoment B raw26787 raw26787Labels = mixedMoment B raw26787step0 raw26787step0Labels := by
      have ha : raw26787step0 = (fun i j => raw26787 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26787step0 raw26787; decide +kernel
      have hl : raw26787step0Labels = raw26787Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26787 raw26787Labels permutation170 permutation2
    _ = mixedMoment B node637 node637Labels := by rfl

def raw26788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26788 raw26788Labels = mixedMoment B node625 node625Labels := by
  calc
    mixedMoment B raw26788 raw26788Labels = mixedMoment B raw26788step0 raw26788step0Labels := by
      have ha : raw26788step0 = (fun i j => raw26788 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26788step0 raw26788; decide +kernel
      have hl : raw26788step0Labels = raw26788Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26788 raw26788Labels permutation173 permutation2
    _ = mixedMoment B node625 node625Labels := by rfl

def raw26789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26789 raw26789Labels = mixedMoment B node625 node625Labels := by
  calc
    mixedMoment B raw26789 raw26789Labels = mixedMoment B raw26789step0 raw26789step0Labels := by
      have ha : raw26789step0 = (fun i j => raw26789 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26789step0 raw26789; decide +kernel
      have hl : raw26789step0Labels = raw26789Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26789 raw26789Labels permutation171 permutation2
    _ = mixedMoment B node625 node625Labels := by rfl

def raw26790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26790 raw26790Labels = mixedMoment B node625 node625Labels := by
  calc
    mixedMoment B raw26790 raw26790Labels = mixedMoment B raw26790step0 raw26790step0Labels := by
      have ha : raw26790step0 = (fun i j => raw26790 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26790step0 raw26790; decide +kernel
      have hl : raw26790step0Labels = raw26790Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26790 raw26790Labels permutation170 permutation2
    _ = mixedMoment B node625 node625Labels := by rfl

def raw26791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26791 raw26791Labels = mixedMoment B node629 node629Labels := by
  calc
    _ = mixedMoment B node629 node629Labels := by rfl

def raw26792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26792 raw26792Labels = mixedMoment B node5202 node5202Labels := by
  calc
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw26793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26793 raw26793Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw26793 raw26793Labels = mixedMoment B raw26793step0 raw26793step0Labels := by
      have hz : ∀ j, raw26793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26793step0 = (fun i j => raw26793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26793step0 raw26793; decide +kernel
      have hl : raw26793step0Labels = raw26793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26793 raw26793Labels permutation346 hz
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw26794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26794 raw26794Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw26794 raw26794Labels = mixedMoment B raw26794step0 raw26794step0Labels := by
      have hz : ∀ j, raw26794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26794step0 = (fun i j => raw26794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26794step0 raw26794; decide +kernel
      have hl : raw26794step0Labels = raw26794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26794 raw26794Labels permutation434 hz
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw26795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26795 raw26795Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw26795 raw26795Labels = mixedMoment B raw26795step0 raw26795step0Labels := by
      have hz : ∀ j, raw26795 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26795step0 = (fun i j => raw26795 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26795step0 raw26795; decide +kernel
      have hl : raw26795step0Labels = raw26795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26795 raw26795Labels permutation520 hz
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw26796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw26796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26796 raw26796Labels = mixedMoment B node5283 node5283Labels := by
  calc
    mixedMoment B raw26796 raw26796Labels = mixedMoment B raw26796step0 raw26796step0Labels := by
      have ha : raw26796step0 = (fun i j => raw26796 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26796step0 raw26796; decide +kernel
      have hl : raw26796step0Labels = raw26796Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26796 raw26796Labels permutation170 permutation2
    _ = mixedMoment B node5283 node5283Labels := by rfl

def raw26797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26797 raw26797Labels = mixedMoment B node4171 node4171Labels := by
  calc
    mixedMoment B raw26797 raw26797Labels = mixedMoment B raw26797step0 raw26797step0Labels := by
      have ha : raw26797step0 = (fun i j => raw26797 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26797step0 raw26797; decide +kernel
      have hl : raw26797step0Labels = raw26797Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26797 raw26797Labels permutation170 permutation3
    mixedMoment B raw26797step0 raw26797step0Labels = mixedMoment B raw26797step1 raw26797step1Labels := by
      have ha : raw26797step1 = raw26797step0 := by apply Matrix.ext; unfold raw26797step1 raw26797step0; decide +kernel
      have hl : raw26797step0Labels = labelEmbedding6 ∘ raw26797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26797step0 raw26797step0Labels raw26797step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4171 node4171Labels := by rfl

def raw26798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26798 raw26798Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26798 raw26798Labels = mixedMoment B raw26798step0 raw26798step0Labels := by
      have hz : ∀ j, raw26798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26798step0 = (fun i j => raw26798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26798step0 raw26798; decide +kernel
      have hl : raw26798step0Labels = raw26798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26798 raw26798Labels permutation346 hz
    mixedMoment B raw26798step0 raw26798step0Labels = mixedMoment B raw26798step1 raw26798step1Labels := by
      have ha : raw26798step1 = (fun i j => raw26798step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26798step1 raw26798step0; decide +kernel
      have hl : raw26798step1Labels = raw26798step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26798step0 raw26798step0Labels permutation40 permutation2
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw26799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26799 raw26799Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26799 raw26799Labels = mixedMoment B raw26799step0 raw26799step0Labels := by
      have hz : ∀ j, raw26799 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26799step0 = (fun i j => raw26799 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26799step0 raw26799; decide +kernel
      have hl : raw26799step0Labels = raw26799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26799 raw26799Labels permutation434 hz
    mixedMoment B raw26799step0 raw26799step0Labels = mixedMoment B raw26799step1 raw26799step1Labels := by
      have ha : raw26799step1 = (fun i j => raw26799step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26799step1 raw26799step0; decide +kernel
      have hl : raw26799step1Labels = raw26799step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26799step0 raw26799step0Labels permutation40 permutation2
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw26800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26800 raw26800Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26800 raw26800Labels = mixedMoment B raw26800step0 raw26800step0Labels := by
      have hz : ∀ j, raw26800 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26800step0 = (fun i j => raw26800 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26800step0 raw26800; decide +kernel
      have hl : raw26800step0Labels = raw26800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26800 raw26800Labels permutation520 hz
    mixedMoment B raw26800step0 raw26800step0Labels = mixedMoment B raw26800step1 raw26800step1Labels := by
      have ha : raw26800step1 = (fun i j => raw26800step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26800step1 raw26800step0; decide +kernel
      have hl : raw26800step1Labels = raw26800step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26800step0 raw26800step0Labels permutation40 permutation2
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw26801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26801 raw26801Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26801 raw26801Labels = mixedMoment B raw26801step0 raw26801step0Labels := by
      have ha : raw26801step0 = (fun i j => raw26801 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26801step0 raw26801; decide +kernel
      have hl : raw26801step0Labels = raw26801Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26801 raw26801Labels permutation246 permutation3
    mixedMoment B raw26801step0 raw26801step0Labels = mixedMoment B raw26801step1 raw26801step1Labels := by
      have ha : raw26801step1 = raw26801step0 := by apply Matrix.ext; unfold raw26801step1 raw26801step0; decide +kernel
      have hl : raw26801step0Labels = labelEmbedding6 ∘ raw26801step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26801step0 raw26801step0Labels raw26801step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw26802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26802step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26802step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26802 raw26802Labels = mixedMoment B node4139 node4139Labels := by
  calc
    mixedMoment B raw26802 raw26802Labels = mixedMoment B raw26802step0 raw26802step0Labels := by
      have ha : raw26802step0 = (fun i j => raw26802 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26802step0 raw26802; decide +kernel
      have hl : raw26802step0Labels = raw26802Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26802 raw26802Labels permutation173 permutation3
    mixedMoment B raw26802step0 raw26802step0Labels = mixedMoment B raw26802step1 raw26802step1Labels := by
      have ha : raw26802step1 = raw26802step0 := by apply Matrix.ext; unfold raw26802step1 raw26802step0; decide +kernel
      have hl : raw26802step0Labels = labelEmbedding6 ∘ raw26802step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26802step0 raw26802step0Labels raw26802step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4139 node4139Labels := by rfl

def raw26803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26803step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26803 raw26803Labels = mixedMoment B node4513 node4513Labels := by
  calc
    mixedMoment B raw26803 raw26803Labels = mixedMoment B raw26803step0 raw26803step0Labels := by
      have ha : raw26803step0 = (fun i j => raw26803 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26803step0 raw26803; decide +kernel
      have hl : raw26803step0Labels = raw26803Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26803 raw26803Labels permutation173 permutation3
    mixedMoment B raw26803step0 raw26803step0Labels = mixedMoment B raw26803step1 raw26803step1Labels := by
      have ha : raw26803step1 = raw26803step0 := by apply Matrix.ext; unfold raw26803step1 raw26803step0; decide +kernel
      have hl : raw26803step0Labels = labelEmbedding6 ∘ raw26803step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26803step0 raw26803step0Labels raw26803step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4513 node4513Labels := by rfl

def raw26804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26804step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26804step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26804 raw26804Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26804 raw26804Labels = mixedMoment B raw26804step0 raw26804step0Labels := by
      have hz : ∀ j, raw26804 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26804step0 = (fun i j => raw26804 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26804step0 raw26804; decide +kernel
      have hl : raw26804step0Labels = raw26804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26804 raw26804Labels permutation434 hz
    mixedMoment B raw26804step0 raw26804step0Labels = mixedMoment B raw26804step1 raw26804step1Labels := by
      have ha : raw26804step1 = (fun i j => raw26804step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26804step1 raw26804step0; decide +kernel
      have hl : raw26804step1Labels = raw26804step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26804step0 raw26804step0Labels permutation37 permutation3
    mixedMoment B raw26804step1 raw26804step1Labels = mixedMoment B raw26804step2 raw26804step2Labels := by
      have ha : raw26804step2 = raw26804step1 := by apply Matrix.ext; unfold raw26804step2 raw26804step1; decide +kernel
      have hl : raw26804step1Labels = labelEmbedding6 ∘ raw26804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26804step1 raw26804step1Labels raw26804step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw26805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26805step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26805step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26805 raw26805Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26805 raw26805Labels = mixedMoment B raw26805step0 raw26805step0Labels := by
      have hz : ∀ j, raw26805 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26805step0 = (fun i j => raw26805 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26805step0 raw26805; decide +kernel
      have hl : raw26805step0Labels = raw26805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26805 raw26805Labels permutation520 hz
    mixedMoment B raw26805step0 raw26805step0Labels = mixedMoment B raw26805step1 raw26805step1Labels := by
      have ha : raw26805step1 = (fun i j => raw26805step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26805step1 raw26805step0; decide +kernel
      have hl : raw26805step1Labels = raw26805step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26805step0 raw26805step0Labels permutation37 permutation3
    mixedMoment B raw26805step1 raw26805step1Labels = mixedMoment B raw26805step2 raw26805step2Labels := by
      have ha : raw26805step2 = raw26805step1 := by apply Matrix.ext; unfold raw26805step2 raw26805step1; decide +kernel
      have hl : raw26805step1Labels = labelEmbedding6 ∘ raw26805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26805step1 raw26805step1Labels raw26805step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw26806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26806step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26806 raw26806Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw26806 raw26806Labels = mixedMoment B raw26806step0 raw26806step0Labels := by
      have ha : raw26806step0 = (fun i j => raw26806 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26806step0 raw26806; decide +kernel
      have hl : raw26806step0Labels = raw26806Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26806 raw26806Labels permutation173 permutation3
    mixedMoment B raw26806step0 raw26806step0Labels = mixedMoment B raw26806step1 raw26806step1Labels := by
      have ha : raw26806step1 = raw26806step0 := by apply Matrix.ext; unfold raw26806step1 raw26806step0; decide +kernel
      have hl : raw26806step0Labels = labelEmbedding6 ∘ raw26806step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26806step0 raw26806step0Labels raw26806step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

def raw26807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26807step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26807step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26807 raw26807Labels = mixedMoment B node4139 node4139Labels := by
  calc
    mixedMoment B raw26807 raw26807Labels = mixedMoment B raw26807step0 raw26807step0Labels := by
      have ha : raw26807step0 = (fun i j => raw26807 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26807step0 raw26807; decide +kernel
      have hl : raw26807step0Labels = raw26807Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26807 raw26807Labels permutation171 permutation3
    mixedMoment B raw26807step0 raw26807step0Labels = mixedMoment B raw26807step1 raw26807step1Labels := by
      have ha : raw26807step1 = raw26807step0 := by apply Matrix.ext; unfold raw26807step1 raw26807step0; decide +kernel
      have hl : raw26807step0Labels = labelEmbedding6 ∘ raw26807step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26807step0 raw26807step0Labels raw26807step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4139 node4139Labels := by rfl

def raw26808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26808step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26808 raw26808Labels = mixedMoment B node4513 node4513Labels := by
  calc
    mixedMoment B raw26808 raw26808Labels = mixedMoment B raw26808step0 raw26808step0Labels := by
      have ha : raw26808step0 = (fun i j => raw26808 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26808step0 raw26808; decide +kernel
      have hl : raw26808step0Labels = raw26808Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26808 raw26808Labels permutation171 permutation3
    mixedMoment B raw26808step0 raw26808step0Labels = mixedMoment B raw26808step1 raw26808step1Labels := by
      have ha : raw26808step1 = raw26808step0 := by apply Matrix.ext; unfold raw26808step1 raw26808step0; decide +kernel
      have hl : raw26808step0Labels = labelEmbedding6 ∘ raw26808step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26808step0 raw26808step0Labels raw26808step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4513 node4513Labels := by rfl

def raw26809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26809step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26809step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26809 raw26809Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26809 raw26809Labels = mixedMoment B raw26809step0 raw26809step0Labels := by
      have hz : ∀ j, raw26809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26809step0 = (fun i j => raw26809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26809step0 raw26809; decide +kernel
      have hl : raw26809step0Labels = raw26809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26809 raw26809Labels permutation346 hz
    mixedMoment B raw26809step0 raw26809step0Labels = mixedMoment B raw26809step1 raw26809step1Labels := by
      have ha : raw26809step1 = (fun i j => raw26809step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26809step1 raw26809step0; decide +kernel
      have hl : raw26809step1Labels = raw26809step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26809step0 raw26809step0Labels permutation37 permutation3
    mixedMoment B raw26809step1 raw26809step1Labels = mixedMoment B raw26809step2 raw26809step2Labels := by
      have ha : raw26809step2 = raw26809step1 := by apply Matrix.ext; unfold raw26809step2 raw26809step1; decide +kernel
      have hl : raw26809step1Labels = labelEmbedding6 ∘ raw26809step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26809step1 raw26809step1Labels raw26809step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw26810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26810step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26810step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26810 raw26810Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26810 raw26810Labels = mixedMoment B raw26810step0 raw26810step0Labels := by
      have hz : ∀ j, raw26810 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26810step0 = (fun i j => raw26810 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26810step0 raw26810; decide +kernel
      have hl : raw26810step0Labels = raw26810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26810 raw26810Labels permutation520 hz
    mixedMoment B raw26810step0 raw26810step0Labels = mixedMoment B raw26810step1 raw26810step1Labels := by
      have ha : raw26810step1 = (fun i j => raw26810step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26810step1 raw26810step0; decide +kernel
      have hl : raw26810step1Labels = raw26810step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26810step0 raw26810step0Labels permutation36 permutation3
    mixedMoment B raw26810step1 raw26810step1Labels = mixedMoment B raw26810step2 raw26810step2Labels := by
      have ha : raw26810step2 = raw26810step1 := by apply Matrix.ext; unfold raw26810step2 raw26810step1; decide +kernel
      have hl : raw26810step1Labels = labelEmbedding6 ∘ raw26810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26810step1 raw26810step1Labels raw26810step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw26811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26811step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26811 raw26811Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw26811 raw26811Labels = mixedMoment B raw26811step0 raw26811step0Labels := by
      have ha : raw26811step0 = (fun i j => raw26811 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26811step0 raw26811; decide +kernel
      have hl : raw26811step0Labels = raw26811Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26811 raw26811Labels permutation171 permutation3
    mixedMoment B raw26811step0 raw26811step0Labels = mixedMoment B raw26811step1 raw26811step1Labels := by
      have ha : raw26811step1 = raw26811step0 := by apply Matrix.ext; unfold raw26811step1 raw26811step0; decide +kernel
      have hl : raw26811step0Labels = labelEmbedding6 ∘ raw26811step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26811step0 raw26811step0Labels raw26811step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

def raw26812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26812step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26812 raw26812Labels = mixedMoment B node4139 node4139Labels := by
  calc
    mixedMoment B raw26812 raw26812Labels = mixedMoment B raw26812step0 raw26812step0Labels := by
      have ha : raw26812step0 = (fun i j => raw26812 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26812step0 raw26812; decide +kernel
      have hl : raw26812step0Labels = raw26812Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26812 raw26812Labels permutation170 permutation3
    mixedMoment B raw26812step0 raw26812step0Labels = mixedMoment B raw26812step1 raw26812step1Labels := by
      have ha : raw26812step1 = raw26812step0 := by apply Matrix.ext; unfold raw26812step1 raw26812step0; decide +kernel
      have hl : raw26812step0Labels = labelEmbedding6 ∘ raw26812step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26812step0 raw26812step0Labels raw26812step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4139 node4139Labels := by rfl

def raw26813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26813step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26813 raw26813Labels = mixedMoment B node4513 node4513Labels := by
  calc
    mixedMoment B raw26813 raw26813Labels = mixedMoment B raw26813step0 raw26813step0Labels := by
      have ha : raw26813step0 = (fun i j => raw26813 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26813step0 raw26813; decide +kernel
      have hl : raw26813step0Labels = raw26813Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26813 raw26813Labels permutation170 permutation3
    mixedMoment B raw26813step0 raw26813step0Labels = mixedMoment B raw26813step1 raw26813step1Labels := by
      have ha : raw26813step1 = raw26813step0 := by apply Matrix.ext; unfold raw26813step1 raw26813step0; decide +kernel
      have hl : raw26813step0Labels = labelEmbedding6 ∘ raw26813step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26813step0 raw26813step0Labels raw26813step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4513 node4513Labels := by rfl

def raw26814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26814step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26814step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26814 raw26814Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26814 raw26814Labels = mixedMoment B raw26814step0 raw26814step0Labels := by
      have hz : ∀ j, raw26814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26814step0 = (fun i j => raw26814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26814step0 raw26814; decide +kernel
      have hl : raw26814step0Labels = raw26814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26814 raw26814Labels permutation346 hz
    mixedMoment B raw26814step0 raw26814step0Labels = mixedMoment B raw26814step1 raw26814step1Labels := by
      have ha : raw26814step1 = (fun i j => raw26814step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26814step1 raw26814step0; decide +kernel
      have hl : raw26814step1Labels = raw26814step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26814step0 raw26814step0Labels permutation36 permutation3
    mixedMoment B raw26814step1 raw26814step1Labels = mixedMoment B raw26814step2 raw26814step2Labels := by
      have ha : raw26814step2 = raw26814step1 := by apply Matrix.ext; unfold raw26814step2 raw26814step1; decide +kernel
      have hl : raw26814step1Labels = labelEmbedding6 ∘ raw26814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26814step1 raw26814step1Labels raw26814step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw26815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26815step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26815 raw26815Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26815 raw26815Labels = mixedMoment B raw26815step0 raw26815step0Labels := by
      have hz : ∀ j, raw26815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26815step0 = (fun i j => raw26815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26815step0 raw26815; decide +kernel
      have hl : raw26815step0Labels = raw26815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26815 raw26815Labels permutation434 hz
    mixedMoment B raw26815step0 raw26815step0Labels = mixedMoment B raw26815step1 raw26815step1Labels := by
      have ha : raw26815step1 = (fun i j => raw26815step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26815step1 raw26815step0; decide +kernel
      have hl : raw26815step1Labels = raw26815step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26815step0 raw26815step0Labels permutation36 permutation3
    mixedMoment B raw26815step1 raw26815step1Labels = mixedMoment B raw26815step2 raw26815step2Labels := by
      have ha : raw26815step2 = raw26815step1 := by apply Matrix.ext; unfold raw26815step2 raw26815step1; decide +kernel
      have hl : raw26815step1Labels = labelEmbedding6 ∘ raw26815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26815step1 raw26815step1Labels raw26815step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw26816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw26816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26816step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26816step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26816 raw26816Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw26816 raw26816Labels = mixedMoment B raw26816step0 raw26816step0Labels := by
      have ha : raw26816step0 = (fun i j => raw26816 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26816step0 raw26816; decide +kernel
      have hl : raw26816step0Labels = raw26816Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26816 raw26816Labels permutation170 permutation3
    mixedMoment B raw26816step0 raw26816step0Labels = mixedMoment B raw26816step1 raw26816step1Labels := by
      have ha : raw26816step1 = raw26816step0 := by apply Matrix.ext; unfold raw26816step1 raw26816step0; decide +kernel
      have hl : raw26816step0Labels = labelEmbedding6 ∘ raw26816step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26816step0 raw26816step0Labels raw26816step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

def raw26817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26817step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26817 raw26817Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw26817 raw26817Labels = mixedMoment B raw26817step0 raw26817step0Labels := by
      have ha : raw26817step0 = (fun i j => raw26817 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26817step0 raw26817; decide +kernel
      have hl : raw26817step0Labels = raw26817Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26817 raw26817Labels permutation152 permutation3
    mixedMoment B raw26817step0 raw26817step0Labels = mixedMoment B raw26817step1 raw26817step1Labels := by
      have ha : raw26817step1 = raw26817step0 := by apply Matrix.ext; unfold raw26817step1 raw26817step0; decide +kernel
      have hl : raw26817step0Labels = labelEmbedding6 ∘ raw26817step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26817step0 raw26817step0Labels raw26817step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4143 node4143Labels := by rfl

def raw26818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26818step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26818 raw26818Labels = mixedMoment B node4516 node4516Labels := by
  calc
    mixedMoment B raw26818 raw26818Labels = mixedMoment B raw26818step0 raw26818step0Labels := by
      have ha : raw26818step0 = (fun i j => raw26818 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26818step0 raw26818; decide +kernel
      have hl : raw26818step0Labels = raw26818Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26818 raw26818Labels permutation152 permutation3
    mixedMoment B raw26818step0 raw26818step0Labels = mixedMoment B raw26818step1 raw26818step1Labels := by
      have ha : raw26818step1 = raw26818step0 := by apply Matrix.ext; unfold raw26818step1 raw26818step0; decide +kernel
      have hl : raw26818step0Labels = labelEmbedding6 ∘ raw26818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26818step0 raw26818step0Labels raw26818step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4516 node4516Labels := by rfl

def raw26819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26819step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26819 raw26819Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26819 raw26819Labels = mixedMoment B raw26819step0 raw26819step0Labels := by
      have hz : ∀ j, raw26819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26819step0 = (fun i j => raw26819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26819step0 raw26819; decide +kernel
      have hl : raw26819step0Labels = raw26819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26819 raw26819Labels permutation346 hz
    mixedMoment B raw26819step0 raw26819step0Labels = mixedMoment B raw26819step1 raw26819step1Labels := by
      have ha : raw26819step1 = (fun i j => raw26819step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26819step1 raw26819step0; decide +kernel
      have hl : raw26819step1Labels = raw26819step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26819step0 raw26819step0Labels permutation32 permutation3
    mixedMoment B raw26819step1 raw26819step1Labels = mixedMoment B raw26819step2 raw26819step2Labels := by
      have ha : raw26819step2 = raw26819step1 := by apply Matrix.ext; unfold raw26819step2 raw26819step1; decide +kernel
      have hl : raw26819step1Labels = labelEmbedding6 ∘ raw26819step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26819step1 raw26819step1Labels raw26819step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw26820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26820step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26820 raw26820Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26820 raw26820Labels = mixedMoment B raw26820step0 raw26820step0Labels := by
      have hz : ∀ j, raw26820 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26820step0 = (fun i j => raw26820 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26820step0 raw26820; decide +kernel
      have hl : raw26820step0Labels = raw26820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26820 raw26820Labels permutation434 hz
    mixedMoment B raw26820step0 raw26820step0Labels = mixedMoment B raw26820step1 raw26820step1Labels := by
      have ha : raw26820step1 = (fun i j => raw26820step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26820step1 raw26820step0; decide +kernel
      have hl : raw26820step1Labels = raw26820step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26820step0 raw26820step0Labels permutation32 permutation3
    mixedMoment B raw26820step1 raw26820step1Labels = mixedMoment B raw26820step2 raw26820step2Labels := by
      have ha : raw26820step2 = raw26820step1 := by apply Matrix.ext; unfold raw26820step2 raw26820step1; decide +kernel
      have hl : raw26820step1Labels = labelEmbedding6 ∘ raw26820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26820step1 raw26820step1Labels raw26820step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw26821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw26821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26821step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26821 raw26821Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26821 raw26821Labels = mixedMoment B raw26821step0 raw26821step0Labels := by
      have hz : ∀ j, raw26821 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26821step0 = (fun i j => raw26821 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26821step0 raw26821; decide +kernel
      have hl : raw26821step0Labels = raw26821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26821 raw26821Labels permutation520 hz
    mixedMoment B raw26821step0 raw26821step0Labels = mixedMoment B raw26821step1 raw26821step1Labels := by
      have ha : raw26821step1 = (fun i j => raw26821step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26821step1 raw26821step0; decide +kernel
      have hl : raw26821step1Labels = raw26821step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26821step0 raw26821step0Labels permutation32 permutation3
    mixedMoment B raw26821step1 raw26821step1Labels = mixedMoment B raw26821step2 raw26821step2Labels := by
      have ha : raw26821step2 = raw26821step1 := by apply Matrix.ext; unfold raw26821step2 raw26821step1; decide +kernel
      have hl : raw26821step1Labels = labelEmbedding6 ∘ raw26821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26821step1 raw26821step1Labels raw26821step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw26822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26822 raw26822Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw26822 raw26822Labels = mixedMoment B raw26822step0 raw26822step0Labels := by
      have ha : raw26822step0 = (fun i j => raw26822 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26822step0 raw26822; decide +kernel
      have hl : raw26822step0Labels = raw26822Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26822 raw26822Labels permutation170 permutation3
    _ = mixedMoment B node2880 node2880Labels := by rfl

def raw26823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26823step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26823 raw26823Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw26823 raw26823Labels = mixedMoment B raw26823step0 raw26823step0Labels := by
      have hz : ∀ j, raw26823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26823step0 = (fun i j => raw26823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26823step0 raw26823; decide +kernel
      have hl : raw26823step0Labels = raw26823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26823 raw26823Labels permutation346 hz
    mixedMoment B raw26823step0 raw26823step0Labels = mixedMoment B raw26823step1 raw26823step1Labels := by
      have ha : raw26823step1 = (fun i j => raw26823step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26823step1 raw26823step0; decide +kernel
      have hl : raw26823step1Labels = raw26823step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26823step0 raw26823step0Labels permutation36 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw26824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26824step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26824 raw26824Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw26824 raw26824Labels = mixedMoment B raw26824step0 raw26824step0Labels := by
      have hz : ∀ j, raw26824 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26824step0 = (fun i j => raw26824 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26824step0 raw26824; decide +kernel
      have hl : raw26824step0Labels = raw26824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26824 raw26824Labels permutation434 hz
    mixedMoment B raw26824step0 raw26824step0Labels = mixedMoment B raw26824step1 raw26824step1Labels := by
      have ha : raw26824step1 = (fun i j => raw26824step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26824step1 raw26824step0; decide +kernel
      have hl : raw26824step1Labels = raw26824step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26824step0 raw26824step0Labels permutation36 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw26825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26825step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26825 raw26825Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw26825 raw26825Labels = mixedMoment B raw26825step0 raw26825step0Labels := by
      have hz : ∀ j, raw26825 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26825step0 = (fun i j => raw26825 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26825step0 raw26825; decide +kernel
      have hl : raw26825step0Labels = raw26825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26825 raw26825Labels permutation520 hz
    mixedMoment B raw26825step0 raw26825step0Labels = mixedMoment B raw26825step1 raw26825step1Labels := by
      have ha : raw26825step1 = (fun i j => raw26825step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26825step1 raw26825step0; decide +kernel
      have hl : raw26825step1Labels = raw26825step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26825step0 raw26825step0Labels permutation36 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw26826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26826 raw26826Labels = mixedMoment B node3076 node3076Labels := by
  calc
    mixedMoment B raw26826 raw26826Labels = mixedMoment B raw26826step0 raw26826step0Labels := by
      have ha : raw26826step0 = (fun i j => raw26826 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26826step0 raw26826; decide +kernel
      have hl : raw26826step0Labels = raw26826Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26826 raw26826Labels permutation170 permutation3
    _ = mixedMoment B node3076 node3076Labels := by rfl

def raw26827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26827 raw26827Labels = mixedMoment B node599 node599Labels := by
  calc
    mixedMoment B raw26827 raw26827Labels = mixedMoment B raw26827step0 raw26827step0Labels := by
      have ha : raw26827step0 = (fun i j => raw26827 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26827step0 raw26827; decide +kernel
      have hl : raw26827step0Labels = raw26827Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26827 raw26827Labels permutation170 permutation3
    _ = mixedMoment B node599 node599Labels := by rfl

def raw26828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26828step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26828 raw26828Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26828 raw26828Labels = mixedMoment B raw26828step0 raw26828step0Labels := by
      have hz : ∀ j, raw26828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26828step0 = (fun i j => raw26828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26828step0 raw26828; decide +kernel
      have hl : raw26828step0Labels = raw26828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26828 raw26828Labels permutation346 hz
    mixedMoment B raw26828step0 raw26828step0Labels = mixedMoment B raw26828step1 raw26828step1Labels := by
      have ha : raw26828step1 = (fun i j => raw26828step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26828step1 raw26828step0; decide +kernel
      have hl : raw26828step1Labels = raw26828step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26828step0 raw26828step0Labels permutation36 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw26829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26829step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26829 raw26829Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26829 raw26829Labels = mixedMoment B raw26829step0 raw26829step0Labels := by
      have hz : ∀ j, raw26829 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26829step0 = (fun i j => raw26829 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26829step0 raw26829; decide +kernel
      have hl : raw26829step0Labels = raw26829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26829 raw26829Labels permutation434 hz
    mixedMoment B raw26829step0 raw26829step0Labels = mixedMoment B raw26829step1 raw26829step1Labels := by
      have ha : raw26829step1 = (fun i j => raw26829step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26829step1 raw26829step0; decide +kernel
      have hl : raw26829step1Labels = raw26829step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26829step0 raw26829step0Labels permutation36 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw26830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26830 raw26830Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26830 raw26830Labels = mixedMoment B raw26830step0 raw26830step0Labels := by
      have hz : ∀ j, raw26830 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26830step0 = (fun i j => raw26830 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26830step0 raw26830; decide +kernel
      have hl : raw26830step0Labels = raw26830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26830 raw26830Labels permutation520 hz
    mixedMoment B raw26830step0 raw26830step0Labels = mixedMoment B raw26830step1 raw26830step1Labels := by
      have ha : raw26830step1 = (fun i j => raw26830step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26830step1 raw26830step0; decide +kernel
      have hl : raw26830step1Labels = raw26830step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26830step0 raw26830step0Labels permutation36 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw26831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26831 raw26831Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw26831 raw26831Labels = mixedMoment B raw26831step0 raw26831step0Labels := by
      have ha : raw26831step0 = (fun i j => raw26831 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26831step0 raw26831; decide +kernel
      have hl : raw26831step0Labels = raw26831Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26831 raw26831Labels permutation246 permutation3
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw26832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26832 raw26832Labels = mixedMoment B node567 node567Labels := by
  calc
    mixedMoment B raw26832 raw26832Labels = mixedMoment B raw26832step0 raw26832step0Labels := by
      have ha : raw26832step0 = (fun i j => raw26832 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26832step0 raw26832; decide +kernel
      have hl : raw26832step0Labels = raw26832Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26832 raw26832Labels permutation173 permutation3
    _ = mixedMoment B node567 node567Labels := by rfl

def raw26833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26833 raw26833Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw26833 raw26833Labels = mixedMoment B raw26833step0 raw26833step0Labels := by
      have ha : raw26833step0 = (fun i j => raw26833 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26833step0 raw26833; decide +kernel
      have hl : raw26833step0Labels = raw26833Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26833 raw26833Labels permutation173 permutation3
    _ = mixedMoment B node1097 node1097Labels := by rfl

def raw26834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26834 raw26834Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26834 raw26834Labels = mixedMoment B raw26834step0 raw26834step0Labels := by
      have hz : ∀ j, raw26834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26834step0 = (fun i j => raw26834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26834step0 raw26834; decide +kernel
      have hl : raw26834step0Labels = raw26834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26834 raw26834Labels permutation434 hz
    mixedMoment B raw26834step0 raw26834step0Labels = mixedMoment B raw26834step1 raw26834step1Labels := by
      have ha : raw26834step1 = (fun i j => raw26834step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26834step1 raw26834step0; decide +kernel
      have hl : raw26834step1Labels = raw26834step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26834step0 raw26834step0Labels permutation37 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw26835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26835 raw26835Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26835 raw26835Labels = mixedMoment B raw26835step0 raw26835step0Labels := by
      have hz : ∀ j, raw26835 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26835step0 = (fun i j => raw26835 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26835step0 raw26835; decide +kernel
      have hl : raw26835step0Labels = raw26835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26835 raw26835Labels permutation520 hz
    mixedMoment B raw26835step0 raw26835step0Labels = mixedMoment B raw26835step1 raw26835step1Labels := by
      have ha : raw26835step1 = (fun i j => raw26835step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26835step1 raw26835step0; decide +kernel
      have hl : raw26835step1Labels = raw26835step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26835step0 raw26835step0Labels permutation37 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw26836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26836 raw26836Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw26836 raw26836Labels = mixedMoment B raw26836step0 raw26836step0Labels := by
      have ha : raw26836step0 = (fun i j => raw26836 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26836step0 raw26836; decide +kernel
      have hl : raw26836step0Labels = raw26836Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26836 raw26836Labels permutation173 permutation3
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw26837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26837 raw26837Labels = mixedMoment B node567 node567Labels := by
  calc
    mixedMoment B raw26837 raw26837Labels = mixedMoment B raw26837step0 raw26837step0Labels := by
      have ha : raw26837step0 = (fun i j => raw26837 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26837step0 raw26837; decide +kernel
      have hl : raw26837step0Labels = raw26837Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26837 raw26837Labels permutation171 permutation3
    _ = mixedMoment B node567 node567Labels := by rfl

def raw26838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26838 raw26838Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw26838 raw26838Labels = mixedMoment B raw26838step0 raw26838step0Labels := by
      have ha : raw26838step0 = (fun i j => raw26838 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26838step0 raw26838; decide +kernel
      have hl : raw26838step0Labels = raw26838Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26838 raw26838Labels permutation171 permutation3
    _ = mixedMoment B node1097 node1097Labels := by rfl

def raw26839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26839 raw26839Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26839 raw26839Labels = mixedMoment B raw26839step0 raw26839step0Labels := by
      have hz : ∀ j, raw26839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26839step0 = (fun i j => raw26839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26839step0 raw26839; decide +kernel
      have hl : raw26839step0Labels = raw26839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26839 raw26839Labels permutation346 hz
    mixedMoment B raw26839step0 raw26839step0Labels = mixedMoment B raw26839step1 raw26839step1Labels := by
      have ha : raw26839step1 = (fun i j => raw26839step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26839step1 raw26839step0; decide +kernel
      have hl : raw26839step1Labels = raw26839step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26839step0 raw26839step0Labels permutation37 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw26840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26840 raw26840Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26840 raw26840Labels = mixedMoment B raw26840step0 raw26840step0Labels := by
      have hz : ∀ j, raw26840 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26840step0 = (fun i j => raw26840 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26840step0 raw26840; decide +kernel
      have hl : raw26840step0Labels = raw26840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26840 raw26840Labels permutation520 hz
    mixedMoment B raw26840step0 raw26840step0Labels = mixedMoment B raw26840step1 raw26840step1Labels := by
      have ha : raw26840step1 = (fun i j => raw26840step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26840step1 raw26840step0; decide +kernel
      have hl : raw26840step1Labels = raw26840step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26840step0 raw26840step0Labels permutation36 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw26841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26841 raw26841Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw26841 raw26841Labels = mixedMoment B raw26841step0 raw26841step0Labels := by
      have ha : raw26841step0 = (fun i j => raw26841 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26841step0 raw26841; decide +kernel
      have hl : raw26841step0Labels = raw26841Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26841 raw26841Labels permutation171 permutation3
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw26842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26842 raw26842Labels = mixedMoment B node567 node567Labels := by
  calc
    mixedMoment B raw26842 raw26842Labels = mixedMoment B raw26842step0 raw26842step0Labels := by
      have ha : raw26842step0 = (fun i j => raw26842 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26842step0 raw26842; decide +kernel
      have hl : raw26842step0Labels = raw26842Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26842 raw26842Labels permutation170 permutation3
    _ = mixedMoment B node567 node567Labels := by rfl

def raw26843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26843 raw26843Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw26843 raw26843Labels = mixedMoment B raw26843step0 raw26843step0Labels := by
      have ha : raw26843step0 = (fun i j => raw26843 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26843step0 raw26843; decide +kernel
      have hl : raw26843step0Labels = raw26843Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26843 raw26843Labels permutation170 permutation3
    _ = mixedMoment B node1097 node1097Labels := by rfl

def raw26844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26844 raw26844Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26844 raw26844Labels = mixedMoment B raw26844step0 raw26844step0Labels := by
      have hz : ∀ j, raw26844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26844step0 = (fun i j => raw26844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26844step0 raw26844; decide +kernel
      have hl : raw26844step0Labels = raw26844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26844 raw26844Labels permutation346 hz
    mixedMoment B raw26844step0 raw26844step0Labels = mixedMoment B raw26844step1 raw26844step1Labels := by
      have ha : raw26844step1 = (fun i j => raw26844step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26844step1 raw26844step0; decide +kernel
      have hl : raw26844step1Labels = raw26844step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26844step0 raw26844step0Labels permutation36 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw26845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26845 raw26845Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26845 raw26845Labels = mixedMoment B raw26845step0 raw26845step0Labels := by
      have hz : ∀ j, raw26845 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26845step0 = (fun i j => raw26845 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26845step0 raw26845; decide +kernel
      have hl : raw26845step0Labels = raw26845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26845 raw26845Labels permutation434 hz
    mixedMoment B raw26845step0 raw26845step0Labels = mixedMoment B raw26845step1 raw26845step1Labels := by
      have ha : raw26845step1 = (fun i j => raw26845step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26845step1 raw26845step0; decide +kernel
      have hl : raw26845step1Labels = raw26845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26845step0 raw26845step0Labels permutation36 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw26846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw26846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26846 raw26846Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw26846 raw26846Labels = mixedMoment B raw26846step0 raw26846step0Labels := by
      have ha : raw26846step0 = (fun i j => raw26846 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26846step0 raw26846; decide +kernel
      have hl : raw26846step0Labels = raw26846Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26846 raw26846Labels permutation170 permutation3
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw26847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26847 raw26847Labels = mixedMoment B node571 node571Labels := by
  calc
    mixedMoment B raw26847 raw26847Labels = mixedMoment B raw26847step0 raw26847step0Labels := by
      have ha : raw26847step0 = (fun i j => raw26847 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26847step0 raw26847; decide +kernel
      have hl : raw26847step0Labels = raw26847Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26847 raw26847Labels permutation152 permutation3
    _ = mixedMoment B node571 node571Labels := by rfl

def raw26848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26848 raw26848Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw26848 raw26848Labels = mixedMoment B raw26848step0 raw26848step0Labels := by
      have ha : raw26848step0 = (fun i j => raw26848 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26848step0 raw26848; decide +kernel
      have hl : raw26848step0Labels = raw26848Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26848 raw26848Labels permutation152 permutation3
    _ = mixedMoment B node1100 node1100Labels := by rfl

def raw26849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26849step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26849 raw26849Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw26849 raw26849Labels = mixedMoment B raw26849step0 raw26849step0Labels := by
      have hz : ∀ j, raw26849 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26849step0 = (fun i j => raw26849 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26849step0 raw26849; decide +kernel
      have hl : raw26849step0Labels = raw26849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26849 raw26849Labels permutation346 hz
    mixedMoment B raw26849step0 raw26849step0Labels = mixedMoment B raw26849step1 raw26849step1Labels := by
      have ha : raw26849step1 = (fun i j => raw26849step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26849step1 raw26849step0; decide +kernel
      have hl : raw26849step1Labels = raw26849step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26849step0 raw26849step0Labels permutation32 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw26850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26850 raw26850Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw26850 raw26850Labels = mixedMoment B raw26850step0 raw26850step0Labels := by
      have hz : ∀ j, raw26850 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26850step0 = (fun i j => raw26850 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26850step0 raw26850; decide +kernel
      have hl : raw26850step0Labels = raw26850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26850 raw26850Labels permutation434 hz
    mixedMoment B raw26850step0 raw26850step0Labels = mixedMoment B raw26850step1 raw26850step1Labels := by
      have ha : raw26850step1 = (fun i j => raw26850step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26850step1 raw26850step0; decide +kernel
      have hl : raw26850step1Labels = raw26850step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26850step0 raw26850step0Labels permutation32 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw26851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw26851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26851 raw26851Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw26851 raw26851Labels = mixedMoment B raw26851step0 raw26851step0Labels := by
      have hz : ∀ j, raw26851 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26851step0 = (fun i j => raw26851 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26851step0 raw26851; decide +kernel
      have hl : raw26851step0Labels = raw26851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26851 raw26851Labels permutation520 hz
    mixedMoment B raw26851step0 raw26851step0Labels = mixedMoment B raw26851step1 raw26851step1Labels := by
      have ha : raw26851step1 = (fun i j => raw26851step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26851step1 raw26851step0; decide +kernel
      have hl : raw26851step1Labels = raw26851step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26851step0 raw26851step0Labels permutation32 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw26852 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26852step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26852 raw26852Labels = mixedMoment B node4473 node4473Labels := by
  calc
    mixedMoment B raw26852 raw26852Labels = mixedMoment B raw26852step0 raw26852step0Labels := by
      have ha : raw26852step0 = (fun i j => raw26852 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26852step0 raw26852; decide +kernel
      have hl : raw26852step0Labels = raw26852Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26852 raw26852Labels permutation152 permutation7
    mixedMoment B raw26852step0 raw26852step0Labels = mixedMoment B raw26852step1 raw26852step1Labels := by
      have ha : raw26852step1 = raw26852step0 := by apply Matrix.ext; unfold raw26852step1 raw26852step0; decide +kernel
      have hl : raw26852step0Labels = labelEmbedding10 ∘ raw26852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26852step0 raw26852step0Labels raw26852step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4473 node4473Labels := by rfl

def raw26853 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26853step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26853 raw26853Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw26853 raw26853Labels = mixedMoment B raw26853step0 raw26853step0Labels := by
      have ha : raw26853step0 = (fun i j => raw26853 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26853step0 raw26853; decide +kernel
      have hl : raw26853step0Labels = raw26853Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26853 raw26853Labels permutation160 permutation7
    mixedMoment B raw26853step0 raw26853step0Labels = mixedMoment B raw26853step1 raw26853step1Labels := by
      have ha : raw26853step1 = raw26853step0 := by apply Matrix.ext; unfold raw26853step1 raw26853step0; decide +kernel
      have hl : raw26853step0Labels = labelEmbedding10 ∘ raw26853step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26853step0 raw26853step0Labels raw26853step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw26854 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26854step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26854 raw26854Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw26854 raw26854Labels = mixedMoment B raw26854step0 raw26854step0Labels := by
      have ha : raw26854step0 = (fun i j => raw26854 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26854step0 raw26854; decide +kernel
      have hl : raw26854step0Labels = raw26854Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26854 raw26854Labels permutation154 permutation7
    mixedMoment B raw26854step0 raw26854step0Labels = mixedMoment B raw26854step1 raw26854step1Labels := by
      have ha : raw26854step1 = raw26854step0 := by apply Matrix.ext; unfold raw26854step1 raw26854step0; decide +kernel
      have hl : raw26854step0Labels = labelEmbedding10 ∘ raw26854step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26854step0 raw26854step0Labels raw26854step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw26855 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26855step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26855 raw26855Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw26855 raw26855Labels = mixedMoment B raw26855step0 raw26855step0Labels := by
      have ha : raw26855step0 = (fun i j => raw26855 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26855step0 raw26855; decide +kernel
      have hl : raw26855step0Labels = raw26855Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26855 raw26855Labels permutation152 permutation7
    mixedMoment B raw26855step0 raw26855step0Labels = mixedMoment B raw26855step1 raw26855step1Labels := by
      have ha : raw26855step1 = raw26855step0 := by apply Matrix.ext; unfold raw26855step1 raw26855step0; decide +kernel
      have hl : raw26855step0Labels = labelEmbedding10 ∘ raw26855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26855step0 raw26855step0Labels raw26855step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw26856 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26856step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26856step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26856 raw26856Labels = mixedMoment B node4455 node4455Labels := by
  calc
    mixedMoment B raw26856 raw26856Labels = mixedMoment B raw26856step0 raw26856step0Labels := by
      have ha : raw26856step0 = (fun i j => raw26856 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26856step0 raw26856; decide +kernel
      have hl : raw26856step0Labels = raw26856Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26856 raw26856Labels permutation152 permutation7
    mixedMoment B raw26856step0 raw26856step0Labels = mixedMoment B raw26856step1 raw26856step1Labels := by
      have ha : raw26856step1 = raw26856step0 := by apply Matrix.ext; unfold raw26856step1 raw26856step0; decide +kernel
      have hl : raw26856step0Labels = labelEmbedding10 ∘ raw26856step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26856step0 raw26856step0Labels raw26856step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4455 node4455Labels := by rfl

def raw26857 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26857step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26857 raw26857Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26857 raw26857Labels = mixedMoment B raw26857step0 raw26857step0Labels := by
      have hz : ∀ j, raw26857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26857step0 = (fun i j => raw26857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26857step0 raw26857; decide +kernel
      have hl : raw26857step0Labels = raw26857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26857 raw26857Labels permutation265 hz
    mixedMoment B raw26857step0 raw26857step0Labels = mixedMoment B raw26857step1 raw26857step1Labels := by
      have ha : raw26857step1 = (fun i j => raw26857step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26857step1 raw26857step0; decide +kernel
      have hl : raw26857step1Labels = raw26857step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26857step0 raw26857step0Labels permutation50 permutation6
    mixedMoment B raw26857step1 raw26857step1Labels = mixedMoment B raw26857step2 raw26857step2Labels := by
      have ha : raw26857step2 = raw26857step1 := by apply Matrix.ext; unfold raw26857step2 raw26857step1; decide +kernel
      have hl : raw26857step1Labels = labelEmbedding9 ∘ raw26857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26857step1 raw26857step1Labels raw26857step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw26858 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26858step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26858 raw26858Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26858 raw26858Labels = mixedMoment B raw26858step0 raw26858step0Labels := by
      have hz : ∀ j, raw26858 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26858step0 = (fun i j => raw26858 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26858step0 raw26858; decide +kernel
      have hl : raw26858step0Labels = raw26858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26858 raw26858Labels permutation265 hz
    mixedMoment B raw26858step0 raw26858step0Labels = mixedMoment B raw26858step1 raw26858step1Labels := by
      have ha : raw26858step1 = (fun i j => raw26858step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26858step1 raw26858step0; decide +kernel
      have hl : raw26858step1Labels = raw26858step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26858step0 raw26858step0Labels permutation48 permutation6
    mixedMoment B raw26858step1 raw26858step1Labels = mixedMoment B raw26858step2 raw26858step2Labels := by
      have ha : raw26858step2 = raw26858step1 := by apply Matrix.ext; unfold raw26858step2 raw26858step1; decide +kernel
      have hl : raw26858step1Labels = labelEmbedding9 ∘ raw26858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26858step1 raw26858step1Labels raw26858step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw26859 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26859step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26859step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26859 raw26859Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26859 raw26859Labels = mixedMoment B raw26859step0 raw26859step0Labels := by
      have hz : ∀ j, raw26859 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26859step0 = (fun i j => raw26859 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26859step0 raw26859; decide +kernel
      have hl : raw26859step0Labels = raw26859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26859 raw26859Labels permutation265 hz
    mixedMoment B raw26859step0 raw26859step0Labels = mixedMoment B raw26859step1 raw26859step1Labels := by
      have ha : raw26859step1 = (fun i j => raw26859step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26859step1 raw26859step0; decide +kernel
      have hl : raw26859step1Labels = raw26859step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26859step0 raw26859step0Labels permutation50 permutation6
    mixedMoment B raw26859step1 raw26859step1Labels = mixedMoment B raw26859step2 raw26859step2Labels := by
      have ha : raw26859step2 = raw26859step1 := by apply Matrix.ext; unfold raw26859step2 raw26859step1; decide +kernel
      have hl : raw26859step1Labels = labelEmbedding9 ∘ raw26859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26859step1 raw26859step1Labels raw26859step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw26860 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26860step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26860 raw26860Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw26860 raw26860Labels = mixedMoment B raw26860step0 raw26860step0Labels := by
      have ha : raw26860step0 = (fun i j => raw26860 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26860step0 raw26860; decide +kernel
      have hl : raw26860step0Labels = raw26860Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26860 raw26860Labels permutation173 permutation6
    mixedMoment B raw26860step0 raw26860step0Labels = mixedMoment B raw26860step1 raw26860step1Labels := by
      have ha : raw26860step1 = raw26860step0 := by apply Matrix.ext; unfold raw26860step1 raw26860step0; decide +kernel
      have hl : raw26860step0Labels = labelEmbedding9 ∘ raw26860step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26860step0 raw26860step0Labels raw26860step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw26861 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26861step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26861 raw26861Labels = mixedMoment B node4566 node4566Labels := by
  calc
    mixedMoment B raw26861 raw26861Labels = mixedMoment B raw26861step0 raw26861step0Labels := by
      have ha : raw26861step0 = (fun i j => raw26861 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26861step0 raw26861; decide +kernel
      have hl : raw26861step0Labels = raw26861Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26861 raw26861Labels permutation173 permutation6
    mixedMoment B raw26861step0 raw26861step0Labels = mixedMoment B raw26861step1 raw26861step1Labels := by
      have ha : raw26861step1 = raw26861step0 := by apply Matrix.ext; unfold raw26861step1 raw26861step0; decide +kernel
      have hl : raw26861step0Labels = labelEmbedding9 ∘ raw26861step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26861step0 raw26861step0Labels raw26861step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4566 node4566Labels := by rfl

def raw26862 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26862step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26862 raw26862Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26862 raw26862Labels = mixedMoment B raw26862step0 raw26862step0Labels := by
      have ha : raw26862step0 = (fun i j => raw26862 (permutation163 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26862step0 raw26862; decide +kernel
      have hl : raw26862step0Labels = raw26862Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26862 raw26862Labels permutation163 permutation6
    mixedMoment B raw26862step0 raw26862step0Labels = mixedMoment B raw26862step1 raw26862step1Labels := by
      have ha : raw26862step1 = raw26862step0 := by apply Matrix.ext; unfold raw26862step1 raw26862step0; decide +kernel
      have hl : raw26862step0Labels = labelEmbedding9 ∘ raw26862step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26862step0 raw26862step0Labels raw26862step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26863 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26863step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26863 raw26863Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26863 raw26863Labels = mixedMoment B raw26863step0 raw26863step0Labels := by
      have ha : raw26863step0 = (fun i j => raw26863 (permutation169 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26863step0 raw26863; decide +kernel
      have hl : raw26863step0Labels = raw26863Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26863 raw26863Labels permutation169 permutation6
    mixedMoment B raw26863step0 raw26863step0Labels = mixedMoment B raw26863step1 raw26863step1Labels := by
      have ha : raw26863step1 = raw26863step0 := by apply Matrix.ext; unfold raw26863step1 raw26863step0; decide +kernel
      have hl : raw26863step0Labels = labelEmbedding9 ∘ raw26863step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26863step0 raw26863step0Labels raw26863step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26864 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26864step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26864 raw26864Labels = mixedMoment B node4595 node4595Labels := by
  calc
    mixedMoment B raw26864 raw26864Labels = mixedMoment B raw26864step0 raw26864step0Labels := by
      have ha : raw26864step0 = (fun i j => raw26864 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26864step0 raw26864; decide +kernel
      have hl : raw26864step0Labels = raw26864Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26864 raw26864Labels permutation173 permutation6
    mixedMoment B raw26864step0 raw26864step0Labels = mixedMoment B raw26864step1 raw26864step1Labels := by
      have ha : raw26864step1 = raw26864step0 := by apply Matrix.ext; unfold raw26864step1 raw26864step0; decide +kernel
      have hl : raw26864step0Labels = labelEmbedding9 ∘ raw26864step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26864step0 raw26864step0Labels raw26864step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4595 node4595Labels := by rfl

def raw26865 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26865step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26865 raw26865Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw26865 raw26865Labels = mixedMoment B raw26865step0 raw26865step0Labels := by
      have ha : raw26865step0 = (fun i j => raw26865 (permutation171 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26865step0 raw26865; decide +kernel
      have hl : raw26865step0Labels = raw26865Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26865 raw26865Labels permutation171 permutation6
    mixedMoment B raw26865step0 raw26865step0Labels = mixedMoment B raw26865step1 raw26865step1Labels := by
      have ha : raw26865step1 = raw26865step0 := by apply Matrix.ext; unfold raw26865step1 raw26865step0; decide +kernel
      have hl : raw26865step0Labels = labelEmbedding9 ∘ raw26865step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26865step0 raw26865step0Labels raw26865step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw26866 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26866step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26866 raw26866Labels = mixedMoment B node4566 node4566Labels := by
  calc
    mixedMoment B raw26866 raw26866Labels = mixedMoment B raw26866step0 raw26866step0Labels := by
      have ha : raw26866step0 = (fun i j => raw26866 (permutation171 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26866step0 raw26866; decide +kernel
      have hl : raw26866step0Labels = raw26866Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26866 raw26866Labels permutation171 permutation6
    mixedMoment B raw26866step0 raw26866step0Labels = mixedMoment B raw26866step1 raw26866step1Labels := by
      have ha : raw26866step1 = raw26866step0 := by apply Matrix.ext; unfold raw26866step1 raw26866step0; decide +kernel
      have hl : raw26866step0Labels = labelEmbedding9 ∘ raw26866step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26866step0 raw26866step0Labels raw26866step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4566 node4566Labels := by rfl

def raw26867 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26867step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26867 raw26867Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26867 raw26867Labels = mixedMoment B raw26867step0 raw26867step0Labels := by
      have ha : raw26867step0 = (fun i j => raw26867 (permutation157 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26867step0 raw26867; decide +kernel
      have hl : raw26867step0Labels = raw26867Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26867 raw26867Labels permutation157 permutation6
    mixedMoment B raw26867step0 raw26867step0Labels = mixedMoment B raw26867step1 raw26867step1Labels := by
      have ha : raw26867step1 = raw26867step0 := by apply Matrix.ext; unfold raw26867step1 raw26867step0; decide +kernel
      have hl : raw26867step0Labels = labelEmbedding9 ∘ raw26867step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26867step0 raw26867step0Labels raw26867step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26868 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26868step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26868 raw26868Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26868 raw26868Labels = mixedMoment B raw26868step0 raw26868step0Labels := by
      have ha : raw26868step0 = (fun i j => raw26868 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26868step0 raw26868; decide +kernel
      have hl : raw26868step0Labels = raw26868Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26868 raw26868Labels permutation168 permutation6
    mixedMoment B raw26868step0 raw26868step0Labels = mixedMoment B raw26868step1 raw26868step1Labels := by
      have ha : raw26868step1 = raw26868step0 := by apply Matrix.ext; unfold raw26868step1 raw26868step0; decide +kernel
      have hl : raw26868step0Labels = labelEmbedding9 ∘ raw26868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26868step0 raw26868step0Labels raw26868step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26869 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26869step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26869 raw26869Labels = mixedMoment B node4595 node4595Labels := by
  calc
    mixedMoment B raw26869 raw26869Labels = mixedMoment B raw26869step0 raw26869step0Labels := by
      have ha : raw26869step0 = (fun i j => raw26869 (permutation171 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26869step0 raw26869; decide +kernel
      have hl : raw26869step0Labels = raw26869Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26869 raw26869Labels permutation171 permutation6
    mixedMoment B raw26869step0 raw26869step0Labels = mixedMoment B raw26869step1 raw26869step1Labels := by
      have ha : raw26869step1 = raw26869step0 := by apply Matrix.ext; unfold raw26869step1 raw26869step0; decide +kernel
      have hl : raw26869step0Labels = labelEmbedding9 ∘ raw26869step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26869step0 raw26869step0Labels raw26869step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4595 node4595Labels := by rfl

def raw26870 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw26870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26870step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26870 raw26870Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw26870 raw26870Labels = mixedMoment B raw26870step0 raw26870step0Labels := by
      have ha : raw26870step0 = (fun i j => raw26870 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26870step0 raw26870; decide +kernel
      have hl : raw26870step0Labels = raw26870Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26870 raw26870Labels permutation170 permutation6
    mixedMoment B raw26870step0 raw26870step0Labels = mixedMoment B raw26870step1 raw26870step1Labels := by
      have ha : raw26870step1 = raw26870step0 := by apply Matrix.ext; unfold raw26870step1 raw26870step0; decide +kernel
      have hl : raw26870step0Labels = labelEmbedding9 ∘ raw26870step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26870step0 raw26870step0Labels raw26870step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw26871 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw26871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26871step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26871 raw26871Labels = mixedMoment B node4566 node4566Labels := by
  calc
    mixedMoment B raw26871 raw26871Labels = mixedMoment B raw26871step0 raw26871step0Labels := by
      have ha : raw26871step0 = (fun i j => raw26871 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26871step0 raw26871; decide +kernel
      have hl : raw26871step0Labels = raw26871Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26871 raw26871Labels permutation170 permutation6
    mixedMoment B raw26871step0 raw26871step0Labels = mixedMoment B raw26871step1 raw26871step1Labels := by
      have ha : raw26871step1 = raw26871step0 := by apply Matrix.ext; unfold raw26871step1 raw26871step0; decide +kernel
      have hl : raw26871step0Labels = labelEmbedding9 ∘ raw26871step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26871step0 raw26871step0Labels raw26871step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4566 node4566Labels := by rfl

def raw26872 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw26872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26872step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26872 raw26872Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26872 raw26872Labels = mixedMoment B raw26872step0 raw26872step0Labels := by
      have ha : raw26872step0 = (fun i j => raw26872 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26872step0 raw26872; decide +kernel
      have hl : raw26872step0Labels = raw26872Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26872 raw26872Labels permutation156 permutation6
    mixedMoment B raw26872step0 raw26872step0Labels = mixedMoment B raw26872step1 raw26872step1Labels := by
      have ha : raw26872step1 = raw26872step0 := by apply Matrix.ext; unfold raw26872step1 raw26872step0; decide +kernel
      have hl : raw26872step0Labels = labelEmbedding9 ∘ raw26872step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26872step0 raw26872step0Labels raw26872step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26873 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw26873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26873step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26873 raw26873Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26873 raw26873Labels = mixedMoment B raw26873step0 raw26873step0Labels := by
      have ha : raw26873step0 = (fun i j => raw26873 (permutation162 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26873step0 raw26873; decide +kernel
      have hl : raw26873step0Labels = raw26873Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26873 raw26873Labels permutation162 permutation6
    mixedMoment B raw26873step0 raw26873step0Labels = mixedMoment B raw26873step1 raw26873step1Labels := by
      have ha : raw26873step1 = raw26873step0 := by apply Matrix.ext; unfold raw26873step1 raw26873step0; decide +kernel
      have hl : raw26873step0Labels = labelEmbedding9 ∘ raw26873step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26873step0 raw26873step0Labels raw26873step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26874 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw26874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26874step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26874 raw26874Labels = mixedMoment B node4595 node4595Labels := by
  calc
    mixedMoment B raw26874 raw26874Labels = mixedMoment B raw26874step0 raw26874step0Labels := by
      have ha : raw26874step0 = (fun i j => raw26874 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26874step0 raw26874; decide +kernel
      have hl : raw26874step0Labels = raw26874Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26874 raw26874Labels permutation170 permutation6
    mixedMoment B raw26874step0 raw26874step0Labels = mixedMoment B raw26874step1 raw26874step1Labels := by
      have ha : raw26874step1 = raw26874step0 := by apply Matrix.ext; unfold raw26874step1 raw26874step0; decide +kernel
      have hl : raw26874step0Labels = labelEmbedding9 ∘ raw26874step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26874step0 raw26874step0Labels raw26874step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4595 node4595Labels := by rfl

def raw26875 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26875step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26875step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26875 raw26875Labels = mixedMoment B node4422 node4422Labels := by
  calc
    mixedMoment B raw26875 raw26875Labels = mixedMoment B raw26875step0 raw26875step0Labels := by
      have ha : raw26875step0 = (fun i j => raw26875 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26875step0 raw26875; decide +kernel
      have hl : raw26875step0Labels = raw26875Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26875 raw26875Labels permutation152 permutation6
    mixedMoment B raw26875step0 raw26875step0Labels = mixedMoment B raw26875step1 raw26875step1Labels := by
      have ha : raw26875step1 = raw26875step0 := by apply Matrix.ext; unfold raw26875step1 raw26875step0; decide +kernel
      have hl : raw26875step0Labels = labelEmbedding9 ∘ raw26875step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26875step0 raw26875step0Labels raw26875step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4422 node4422Labels := by rfl

def raw26876 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26876step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26876 raw26876Labels = mixedMoment B node4569 node4569Labels := by
  calc
    mixedMoment B raw26876 raw26876Labels = mixedMoment B raw26876step0 raw26876step0Labels := by
      have ha : raw26876step0 = (fun i j => raw26876 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26876step0 raw26876; decide +kernel
      have hl : raw26876step0Labels = raw26876Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26876 raw26876Labels permutation152 permutation6
    mixedMoment B raw26876step0 raw26876step0Labels = mixedMoment B raw26876step1 raw26876step1Labels := by
      have ha : raw26876step1 = raw26876step0 := by apply Matrix.ext; unfold raw26876step1 raw26876step0; decide +kernel
      have hl : raw26876step0Labels = labelEmbedding9 ∘ raw26876step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26876step0 raw26876step0Labels raw26876step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4569 node4569Labels := by rfl

def raw26877 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26877step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26877step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26877 raw26877Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26877 raw26877Labels = mixedMoment B raw26877step0 raw26877step0Labels := by
      have ha : raw26877step0 = (fun i j => raw26877 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26877step0 raw26877; decide +kernel
      have hl : raw26877step0Labels = raw26877Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26877 raw26877Labels permutation164 permutation6
    mixedMoment B raw26877step0 raw26877step0Labels = mixedMoment B raw26877step1 raw26877step1Labels := by
      have ha : raw26877step1 = raw26877step0 := by apply Matrix.ext; unfold raw26877step1 raw26877step0; decide +kernel
      have hl : raw26877step0Labels = labelEmbedding9 ∘ raw26877step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26877step0 raw26877step0Labels raw26877step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw26878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26878 raw26878Labels = mixedMoment B node1183 node1183Labels := by
  calc
    mixedMoment B raw26878 raw26878Labels = mixedMoment B raw26878step0 raw26878step0Labels := by
      have ha : raw26878step0 = (fun i j => raw26878 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26878step0 raw26878; decide +kernel
      have hl : raw26878step0Labels = raw26878Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26878 raw26878Labels permutation173 permutation2
    _ = mixedMoment B node1183 node1183Labels := by rfl

def raw26879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26879 raw26879Labels = mixedMoment B node2398 node2398Labels := by
  calc
    mixedMoment B raw26879 raw26879Labels = mixedMoment B raw26879step0 raw26879step0Labels := by
      have ha : raw26879step0 = (fun i j => raw26879 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26879step0 raw26879; decide +kernel
      have hl : raw26879step0Labels = raw26879Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26879 raw26879Labels permutation173 permutation2
    _ = mixedMoment B node2398 node2398Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
