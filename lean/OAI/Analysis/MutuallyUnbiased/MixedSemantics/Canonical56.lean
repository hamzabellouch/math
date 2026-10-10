import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw7168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7168 raw7168Labels = mixedMoment B node3282 node3282Labels := by
  calc
    mixedMoment B raw7168 raw7168Labels = mixedMoment B raw7168step0 raw7168step0Labels := by
      have ha : raw7168step0 = (fun i j => raw7168 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7168step0 raw7168; decide +kernel
      have hl : raw7168step0Labels = raw7168Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7168 raw7168Labels permutation185 permutation5
    mixedMoment B raw7168step0 raw7168step0Labels = mixedMoment B raw7168step1 raw7168step1Labels := by
      have ha : raw7168step1 = -raw7168step0 := by apply Matrix.ext; change ∀ i j, raw7168step1 i j = -(raw7168step0 i j); unfold raw7168step1 raw7168step0; decide +kernel
      have hl : raw7168step1Labels = raw7168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7168step1 raw7168step1Labels = mixedMoment B raw7168step2 raw7168step2Labels := by
      have ha : raw7168step2 = raw7168step1 := by apply Matrix.ext; unfold raw7168step2 raw7168step1; decide +kernel
      have hl : raw7168step1Labels = labelEmbedding1 ∘ raw7168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7168step1 raw7168step1Labels raw7168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3282 node3282Labels := by rfl

def raw7169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7169step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7169step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7169 raw7169Labels = mixedMoment B node3568 node3568Labels := by
  calc
    mixedMoment B raw7169 raw7169Labels = mixedMoment B raw7169step0 raw7169step0Labels := by
      have ha : raw7169step0 = (fun i j => raw7169 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7169step0 raw7169; decide +kernel
      have hl : raw7169step0Labels = raw7169Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7169 raw7169Labels permutation164 permutation7
    mixedMoment B raw7169step0 raw7169step0Labels = mixedMoment B raw7169step1 raw7169step1Labels := by
      have ha : raw7169step1 = -raw7169step0 := by apply Matrix.ext; change ∀ i j, raw7169step1 i j = -(raw7169step0 i j); unfold raw7169step1 raw7169step0; decide +kernel
      have hl : raw7169step1Labels = raw7169step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7169step1 raw7169step1Labels = mixedMoment B raw7169step2 raw7169step2Labels := by
      have ha : raw7169step2 = raw7169step1 := by apply Matrix.ext; unfold raw7169step2 raw7169step1; decide +kernel
      have hl : raw7169step1Labels = labelEmbedding1 ∘ raw7169step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7169step1 raw7169step1Labels raw7169step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3568 node3568Labels := by rfl

def raw7170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7170step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7170step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7170 raw7170Labels = mixedMoment B node3568 node3568Labels := by
  calc
    mixedMoment B raw7170 raw7170Labels = mixedMoment B raw7170step0 raw7170step0Labels := by
      have ha : raw7170step0 = (fun i j => raw7170 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7170step0 raw7170; decide +kernel
      have hl : raw7170step0Labels = raw7170Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7170 raw7170Labels permutation166 permutation7
    mixedMoment B raw7170step0 raw7170step0Labels = mixedMoment B raw7170step1 raw7170step1Labels := by
      have ha : raw7170step1 = -raw7170step0 := by apply Matrix.ext; change ∀ i j, raw7170step1 i j = -(raw7170step0 i j); unfold raw7170step1 raw7170step0; decide +kernel
      have hl : raw7170step1Labels = raw7170step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7170step1 raw7170step1Labels = mixedMoment B raw7170step2 raw7170step2Labels := by
      have ha : raw7170step2 = raw7170step1 := by apply Matrix.ext; unfold raw7170step2 raw7170step1; decide +kernel
      have hl : raw7170step1Labels = labelEmbedding1 ∘ raw7170step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7170step1 raw7170step1Labels raw7170step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3568 node3568Labels := by rfl

def raw7171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7171step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7171step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7171step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7171step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7171 raw7171Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw7171 raw7171Labels = mixedMoment B raw7171step0 raw7171step0Labels := by
      have hz : ∀ j, raw7171 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7171step0 = (fun i j => raw7171 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7171step0 raw7171; decide +kernel
      have hl : raw7171step0Labels = raw7171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7171 raw7171Labels permutation520 hz
    mixedMoment B raw7171step0 raw7171step0Labels = mixedMoment B raw7171step1 raw7171step1Labels := by
      have ha : raw7171step1 = (fun i j => raw7171step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7171step1 raw7171step0; decide +kernel
      have hl : raw7171step1Labels = raw7171step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7171step0 raw7171step0Labels permutation32 permutation7
    mixedMoment B raw7171step1 raw7171step1Labels = mixedMoment B raw7171step2 raw7171step2Labels := by
      have ha : raw7171step2 = -raw7171step1 := by apply Matrix.ext; change ∀ i j, raw7171step2 i j = -(raw7171step1 i j); unfold raw7171step2 raw7171step1; decide +kernel
      have hl : raw7171step2Labels = raw7171step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7171step2 raw7171step2Labels = mixedMoment B raw7171step3 raw7171step3Labels := by
      have ha : raw7171step3 = raw7171step2 := by apply Matrix.ext; unfold raw7171step3 raw7171step2; decide +kernel
      have hl : raw7171step2Labels = labelEmbedding1 ∘ raw7171step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7171step2 raw7171step2Labels raw7171step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw7172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7172step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7172step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7172 raw7172Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw7172 raw7172Labels = mixedMoment B raw7172step0 raw7172step0Labels := by
      have ha : raw7172step0 = (fun i j => raw7172 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7172step0 raw7172; decide +kernel
      have hl : raw7172step0Labels = raw7172Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7172 raw7172Labels permutation164 permutation7
    mixedMoment B raw7172step0 raw7172step0Labels = mixedMoment B raw7172step1 raw7172step1Labels := by
      have ha : raw7172step1 = -raw7172step0 := by apply Matrix.ext; change ∀ i j, raw7172step1 i j = -(raw7172step0 i j); unfold raw7172step1 raw7172step0; decide +kernel
      have hl : raw7172step1Labels = raw7172step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7172step1 raw7172step1Labels = mixedMoment B raw7172step2 raw7172step2Labels := by
      have ha : raw7172step2 = raw7172step1 := by apply Matrix.ext; unfold raw7172step2 raw7172step1; decide +kernel
      have hl : raw7172step1Labels = labelEmbedding1 ∘ raw7172step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7172step1 raw7172step1Labels raw7172step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw7173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7173step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7173step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7173 raw7173Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw7173 raw7173Labels = mixedMoment B raw7173step0 raw7173step0Labels := by
      have ha : raw7173step0 = (fun i j => raw7173 (permutation206 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7173step0 raw7173; decide +kernel
      have hl : raw7173step0Labels = raw7173Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7173 raw7173Labels permutation206 permutation5
    mixedMoment B raw7173step0 raw7173step0Labels = mixedMoment B raw7173step1 raw7173step1Labels := by
      have ha : raw7173step1 = -raw7173step0 := by apply Matrix.ext; change ∀ i j, raw7173step1 i j = -(raw7173step0 i j); unfold raw7173step1 raw7173step0; decide +kernel
      have hl : raw7173step1Labels = raw7173step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7173step1 raw7173step1Labels = mixedMoment B raw7173step2 raw7173step2Labels := by
      have ha : raw7173step2 = raw7173step1 := by apply Matrix.ext; unfold raw7173step2 raw7173step1; decide +kernel
      have hl : raw7173step1Labels = labelEmbedding1 ∘ raw7173step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7173step1 raw7173step1Labels raw7173step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw7174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7174step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7174 raw7174Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw7174 raw7174Labels = mixedMoment B raw7174step0 raw7174step0Labels := by
      have ha : raw7174step0 = (fun i j => raw7174 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7174step0 raw7174; decide +kernel
      have hl : raw7174step0Labels = raw7174Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7174 raw7174Labels permutation166 permutation7
    mixedMoment B raw7174step0 raw7174step0Labels = mixedMoment B raw7174step1 raw7174step1Labels := by
      have ha : raw7174step1 = -raw7174step0 := by apply Matrix.ext; change ∀ i j, raw7174step1 i j = -(raw7174step0 i j); unfold raw7174step1 raw7174step0; decide +kernel
      have hl : raw7174step1Labels = raw7174step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7174step1 raw7174step1Labels = mixedMoment B raw7174step2 raw7174step2Labels := by
      have ha : raw7174step2 = raw7174step1 := by apply Matrix.ext; unfold raw7174step2 raw7174step1; decide +kernel
      have hl : raw7174step1Labels = labelEmbedding1 ∘ raw7174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7174step1 raw7174step1Labels raw7174step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw7175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw7175step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7175step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7175 raw7175Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw7175 raw7175Labels = mixedMoment B raw7175step0 raw7175step0Labels := by
      have ha : raw7175step0 = (fun i j => raw7175 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7175step0 raw7175; decide +kernel
      have hl : raw7175step0Labels = raw7175Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7175 raw7175Labels permutation166 permutation7
    mixedMoment B raw7175step0 raw7175step0Labels = mixedMoment B raw7175step1 raw7175step1Labels := by
      have ha : raw7175step1 = -raw7175step0 := by apply Matrix.ext; change ∀ i j, raw7175step1 i j = -(raw7175step0 i j); unfold raw7175step1 raw7175step0; decide +kernel
      have hl : raw7175step1Labels = raw7175step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7175step1 raw7175step1Labels = mixedMoment B raw7175step2 raw7175step2Labels := by
      have ha : raw7175step2 = raw7175step1 := by apply Matrix.ext; unfold raw7175step2 raw7175step1; decide +kernel
      have hl : raw7175step1Labels = labelEmbedding1 ∘ raw7175step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7175step1 raw7175step1Labels raw7175step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw7176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7176step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7176step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7176 raw7176Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw7176 raw7176Labels = mixedMoment B raw7176step0 raw7176step0Labels := by
      have hz : ∀ j, raw7176 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7176step0 = (fun i j => raw7176 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7176step0 raw7176; decide +kernel
      have hl : raw7176step0Labels = raw7176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7176 raw7176Labels permutation520 hz
    mixedMoment B raw7176step0 raw7176step0Labels = mixedMoment B raw7176step1 raw7176step1Labels := by
      have ha : raw7176step1 = (fun i j => raw7176step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7176step1 raw7176step0; decide +kernel
      have hl : raw7176step1Labels = raw7176step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7176step0 raw7176step0Labels permutation34 permutation7
    mixedMoment B raw7176step1 raw7176step1Labels = mixedMoment B raw7176step2 raw7176step2Labels := by
      have ha : raw7176step2 = -raw7176step1 := by apply Matrix.ext; change ∀ i j, raw7176step2 i j = -(raw7176step1 i j); unfold raw7176step2 raw7176step1; decide +kernel
      have hl : raw7176step2Labels = raw7176step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7176step2 raw7176step2Labels = mixedMoment B raw7176step3 raw7176step3Labels := by
      have ha : raw7176step3 = raw7176step2 := by apply Matrix.ext; unfold raw7176step3 raw7176step2; decide +kernel
      have hl : raw7176step2Labels = labelEmbedding1 ∘ raw7176step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7176step2 raw7176step2Labels raw7176step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw7177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7177step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7177step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7177 raw7177Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw7177 raw7177Labels = mixedMoment B raw7177step0 raw7177step0Labels := by
      have ha : raw7177step0 = (fun i j => raw7177 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7177step0 raw7177; decide +kernel
      have hl : raw7177step0Labels = raw7177Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7177 raw7177Labels permutation166 permutation7
    mixedMoment B raw7177step0 raw7177step0Labels = mixedMoment B raw7177step1 raw7177step1Labels := by
      have ha : raw7177step1 = -raw7177step0 := by apply Matrix.ext; change ∀ i j, raw7177step1 i j = -(raw7177step0 i j); unfold raw7177step1 raw7177step0; decide +kernel
      have hl : raw7177step1Labels = raw7177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7177step1 raw7177step1Labels = mixedMoment B raw7177step2 raw7177step2Labels := by
      have ha : raw7177step2 = raw7177step1 := by apply Matrix.ext; unfold raw7177step2 raw7177step1; decide +kernel
      have hl : raw7177step1Labels = labelEmbedding1 ∘ raw7177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7177step1 raw7177step1Labels raw7177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw7178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7178step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7178 raw7178Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw7178 raw7178Labels = mixedMoment B raw7178step0 raw7178step0Labels := by
      have ha : raw7178step0 = (fun i j => raw7178 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7178step0 raw7178; decide +kernel
      have hl : raw7178step0Labels = raw7178Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7178 raw7178Labels permutation182 permutation5
    mixedMoment B raw7178step0 raw7178step0Labels = mixedMoment B raw7178step1 raw7178step1Labels := by
      have ha : raw7178step1 = -raw7178step0 := by apply Matrix.ext; change ∀ i j, raw7178step1 i j = -(raw7178step0 i j); unfold raw7178step1 raw7178step0; decide +kernel
      have hl : raw7178step1Labels = raw7178step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7178step1 raw7178step1Labels = mixedMoment B raw7178step2 raw7178step2Labels := by
      have ha : raw7178step2 = raw7178step1 := by apply Matrix.ext; unfold raw7178step2 raw7178step1; decide +kernel
      have hl : raw7178step1Labels = labelEmbedding1 ∘ raw7178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7178step1 raw7178step1Labels raw7178step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw7179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7179step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7179step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7179step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7179 raw7179Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw7179 raw7179Labels = mixedMoment B raw7179step0 raw7179step0Labels := by
      have ha : raw7179step0 = (fun i j => raw7179 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7179step0 raw7179; decide +kernel
      have hl : raw7179step0Labels = raw7179Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7179 raw7179Labels permutation164 permutation7
    mixedMoment B raw7179step0 raw7179step0Labels = mixedMoment B raw7179step1 raw7179step1Labels := by
      have ha : raw7179step1 = -raw7179step0 := by apply Matrix.ext; change ∀ i j, raw7179step1 i j = -(raw7179step0 i j); unfold raw7179step1 raw7179step0; decide +kernel
      have hl : raw7179step1Labels = raw7179step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7179step1 raw7179step1Labels = mixedMoment B raw7179step2 raw7179step2Labels := by
      have ha : raw7179step2 = raw7179step1 := by apply Matrix.ext; unfold raw7179step2 raw7179step1; decide +kernel
      have hl : raw7179step1Labels = labelEmbedding1 ∘ raw7179step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7179step1 raw7179step1Labels raw7179step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw7180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw7180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7180step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7180 raw7180Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw7180 raw7180Labels = mixedMoment B raw7180step0 raw7180step0Labels := by
      have ha : raw7180step0 = (fun i j => raw7180 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7180step0 raw7180; decide +kernel
      have hl : raw7180step0Labels = raw7180Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7180 raw7180Labels permutation164 permutation7
    mixedMoment B raw7180step0 raw7180step0Labels = mixedMoment B raw7180step1 raw7180step1Labels := by
      have ha : raw7180step1 = -raw7180step0 := by apply Matrix.ext; change ∀ i j, raw7180step1 i j = -(raw7180step0 i j); unfold raw7180step1 raw7180step0; decide +kernel
      have hl : raw7180step1Labels = raw7180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7180step1 raw7180step1Labels = mixedMoment B raw7180step2 raw7180step2Labels := by
      have ha : raw7180step2 = raw7180step1 := by apply Matrix.ext; unfold raw7180step2 raw7180step1; decide +kernel
      have hl : raw7180step1Labels = labelEmbedding1 ∘ raw7180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7180step1 raw7180step1Labels raw7180step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw7181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7181step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7181step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7181step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7181step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7181 raw7181Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw7181 raw7181Labels = mixedMoment B raw7181step0 raw7181step0Labels := by
      have hz : ∀ j, raw7181 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7181step0 = (fun i j => raw7181 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7181step0 raw7181; decide +kernel
      have hl : raw7181step0Labels = raw7181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7181 raw7181Labels permutation520 hz
    mixedMoment B raw7181step0 raw7181step0Labels = mixedMoment B raw7181step1 raw7181step1Labels := by
      have ha : raw7181step1 = (fun i j => raw7181step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7181step1 raw7181step0; decide +kernel
      have hl : raw7181step1Labels = raw7181step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7181step0 raw7181step0Labels permutation32 permutation7
    mixedMoment B raw7181step1 raw7181step1Labels = mixedMoment B raw7181step2 raw7181step2Labels := by
      have ha : raw7181step2 = -raw7181step1 := by apply Matrix.ext; change ∀ i j, raw7181step2 i j = -(raw7181step1 i j); unfold raw7181step2 raw7181step1; decide +kernel
      have hl : raw7181step2Labels = raw7181step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7181step2 raw7181step2Labels = mixedMoment B raw7181step3 raw7181step3Labels := by
      have ha : raw7181step3 = raw7181step2 := by apply Matrix.ext; unfold raw7181step3 raw7181step2; decide +kernel
      have hl : raw7181step2Labels = labelEmbedding1 ∘ raw7181step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7181step2 raw7181step2Labels raw7181step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw7182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7182step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7182 raw7182Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw7182 raw7182Labels = mixedMoment B raw7182step0 raw7182step0Labels := by
      have ha : raw7182step0 = (fun i j => raw7182 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7182step0 raw7182; decide +kernel
      have hl : raw7182step0Labels = raw7182Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7182 raw7182Labels permutation164 permutation7
    mixedMoment B raw7182step0 raw7182step0Labels = mixedMoment B raw7182step1 raw7182step1Labels := by
      have ha : raw7182step1 = -raw7182step0 := by apply Matrix.ext; change ∀ i j, raw7182step1 i j = -(raw7182step0 i j); unfold raw7182step1 raw7182step0; decide +kernel
      have hl : raw7182step1Labels = raw7182step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7182step1 raw7182step1Labels = mixedMoment B raw7182step2 raw7182step2Labels := by
      have ha : raw7182step2 = raw7182step1 := by apply Matrix.ext; unfold raw7182step2 raw7182step1; decide +kernel
      have hl : raw7182step1Labels = labelEmbedding1 ∘ raw7182step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7182step1 raw7182step1Labels raw7182step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw7183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw7183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7183 raw7183Labels = mixedMoment B node3280 node3280Labels := by
  calc
    mixedMoment B raw7183 raw7183Labels = mixedMoment B raw7183step0 raw7183step0Labels := by
      have ha : raw7183step0 = (fun i j => raw7183 (permutation183 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7183step0 raw7183; decide +kernel
      have hl : raw7183step0Labels = raw7183Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7183 raw7183Labels permutation183 permutation5
    mixedMoment B raw7183step0 raw7183step0Labels = mixedMoment B raw7183step1 raw7183step1Labels := by
      have ha : raw7183step1 = -raw7183step0 := by apply Matrix.ext; change ∀ i j, raw7183step1 i j = -(raw7183step0 i j); unfold raw7183step1 raw7183step0; decide +kernel
      have hl : raw7183step1Labels = raw7183step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7183step1 raw7183step1Labels = mixedMoment B raw7183step2 raw7183step2Labels := by
      have ha : raw7183step2 = raw7183step1 := by apply Matrix.ext; unfold raw7183step2 raw7183step1; decide +kernel
      have hl : raw7183step1Labels = labelEmbedding1 ∘ raw7183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7183step1 raw7183step1Labels raw7183step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3280 node3280Labels := by rfl

def raw7184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7184step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7184 raw7184Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw7184 raw7184Labels = mixedMoment B raw7184step0 raw7184step0Labels := by
      have ha : raw7184step0 = (fun i j => raw7184 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7184step0 raw7184; decide +kernel
      have hl : raw7184step0Labels = raw7184Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7184 raw7184Labels permutation164 permutation7
    mixedMoment B raw7184step0 raw7184step0Labels = mixedMoment B raw7184step1 raw7184step1Labels := by
      have ha : raw7184step1 = -raw7184step0 := by apply Matrix.ext; change ∀ i j, raw7184step1 i j = -(raw7184step0 i j); unfold raw7184step1 raw7184step0; decide +kernel
      have hl : raw7184step1Labels = raw7184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7184step1 raw7184step1Labels = mixedMoment B raw7184step2 raw7184step2Labels := by
      have ha : raw7184step2 = raw7184step1 := by apply Matrix.ext; unfold raw7184step2 raw7184step1; decide +kernel
      have hl : raw7184step1Labels = labelEmbedding1 ∘ raw7184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7184step1 raw7184step1Labels raw7184step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

def raw7185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7185step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7185step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7185step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7185 raw7185Labels = mixedMoment B node3536 node3536Labels := by
  calc
    mixedMoment B raw7185 raw7185Labels = mixedMoment B raw7185step0 raw7185step0Labels := by
      have ha : raw7185step0 = (fun i j => raw7185 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7185step0 raw7185; decide +kernel
      have hl : raw7185step0Labels = raw7185Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7185 raw7185Labels permutation164 permutation7
    mixedMoment B raw7185step0 raw7185step0Labels = mixedMoment B raw7185step1 raw7185step1Labels := by
      have ha : raw7185step1 = -raw7185step0 := by apply Matrix.ext; change ∀ i j, raw7185step1 i j = -(raw7185step0 i j); unfold raw7185step1 raw7185step0; decide +kernel
      have hl : raw7185step1Labels = raw7185step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7185step1 raw7185step1Labels = mixedMoment B raw7185step2 raw7185step2Labels := by
      have ha : raw7185step2 = raw7185step1 := by apply Matrix.ext; unfold raw7185step2 raw7185step1; decide +kernel
      have hl : raw7185step1Labels = labelEmbedding1 ∘ raw7185step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7185step1 raw7185step1Labels raw7185step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3536 node3536Labels := by rfl

def raw7186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7186step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7186 raw7186Labels = mixedMoment B node3536 node3536Labels := by
  calc
    mixedMoment B raw7186 raw7186Labels = mixedMoment B raw7186step0 raw7186step0Labels := by
      have ha : raw7186step0 = (fun i j => raw7186 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7186step0 raw7186; decide +kernel
      have hl : raw7186step0Labels = raw7186Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7186 raw7186Labels permutation166 permutation7
    mixedMoment B raw7186step0 raw7186step0Labels = mixedMoment B raw7186step1 raw7186step1Labels := by
      have ha : raw7186step1 = -raw7186step0 := by apply Matrix.ext; change ∀ i j, raw7186step1 i j = -(raw7186step0 i j); unfold raw7186step1 raw7186step0; decide +kernel
      have hl : raw7186step1Labels = raw7186step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7186step1 raw7186step1Labels = mixedMoment B raw7186step2 raw7186step2Labels := by
      have ha : raw7186step2 = raw7186step1 := by apply Matrix.ext; unfold raw7186step2 raw7186step1; decide +kernel
      have hl : raw7186step1Labels = labelEmbedding1 ∘ raw7186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7186step1 raw7186step1Labels raw7186step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3536 node3536Labels := by rfl

def raw7187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7187 raw7187Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw7187 raw7187Labels = mixedMoment B raw7187step0 raw7187step0Labels := by
      have ha : raw7187step0 = (fun i j => raw7187 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7187step0 raw7187; decide +kernel
      have hl : raw7187step0Labels = raw7187Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7187 raw7187Labels permutation164 permutation7
    mixedMoment B raw7187step0 raw7187step0Labels = mixedMoment B raw7187step1 raw7187step1Labels := by
      have ha : raw7187step1 = -raw7187step0 := by apply Matrix.ext; change ∀ i j, raw7187step1 i j = -(raw7187step0 i j); unfold raw7187step1 raw7187step0; decide +kernel
      have hl : raw7187step1Labels = raw7187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7187step1 raw7187step1Labels = mixedMoment B raw7187step2 raw7187step2Labels := by
      have ha : raw7187step2 = raw7187step1 := by apply Matrix.ext; unfold raw7187step2 raw7187step1; decide +kernel
      have hl : raw7187step1Labels = labelEmbedding1 ∘ raw7187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7187step1 raw7187step1Labels raw7187step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw7188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw7188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw7188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7188step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw7188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7188 raw7188Labels = mixedMoment B node3279 node3279Labels := by
  calc
    mixedMoment B raw7188 raw7188Labels = mixedMoment B raw7188step0 raw7188step0Labels := by
      have ha : raw7188step0 = (fun i j => raw7188 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7188step0 raw7188; decide +kernel
      have hl : raw7188step0Labels = raw7188Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7188 raw7188Labels permutation182 permutation5
    mixedMoment B raw7188step0 raw7188step0Labels = mixedMoment B raw7188step1 raw7188step1Labels := by
      have ha : raw7188step1 = -raw7188step0 := by apply Matrix.ext; change ∀ i j, raw7188step1 i j = -(raw7188step0 i j); unfold raw7188step1 raw7188step0; decide +kernel
      have hl : raw7188step1Labels = raw7188step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7188step1 raw7188step1Labels = mixedMoment B raw7188step2 raw7188step2Labels := by
      have ha : raw7188step2 = raw7188step1 := by apply Matrix.ext; unfold raw7188step2 raw7188step1; decide +kernel
      have hl : raw7188step1Labels = labelEmbedding1 ∘ raw7188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7188step1 raw7188step1Labels raw7188step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3279 node3279Labels := by rfl

def raw7189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7189step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7189step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7189 raw7189Labels = mixedMoment B node3466 node3466Labels := by
  calc
    mixedMoment B raw7189 raw7189Labels = mixedMoment B raw7189step0 raw7189step0Labels := by
      have ha : raw7189step0 = (fun i j => raw7189 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7189step0 raw7189; decide +kernel
      have hl : raw7189step0Labels = raw7189Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7189 raw7189Labels permutation674 permutation5
    mixedMoment B raw7189step0 raw7189step0Labels = mixedMoment B raw7189step1 raw7189step1Labels := by
      have ha : raw7189step1 = raw7189step0 := by apply Matrix.ext; unfold raw7189step1 raw7189step0; decide +kernel
      have hl : raw7189step0Labels = labelEmbedding1 ∘ raw7189step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7189step0 raw7189step0Labels raw7189step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3466 node3466Labels := by rfl

def raw7190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7190step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7190 raw7190Labels = mixedMoment B node3434 node3434Labels := by
  calc
    mixedMoment B raw7190 raw7190Labels = mixedMoment B raw7190step0 raw7190step0Labels := by
      have ha : raw7190step0 = (fun i j => raw7190 (permutation675 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7190step0 raw7190; decide +kernel
      have hl : raw7190step0Labels = raw7190Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7190 raw7190Labels permutation675 permutation5
    mixedMoment B raw7190step0 raw7190step0Labels = mixedMoment B raw7190step1 raw7190step1Labels := by
      have ha : raw7190step1 = raw7190step0 := by apply Matrix.ext; unfold raw7190step1 raw7190step0; decide +kernel
      have hl : raw7190step0Labels = labelEmbedding1 ∘ raw7190step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7190step0 raw7190step0Labels raw7190step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3434 node3434Labels := by rfl

def raw7191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7191step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7191 raw7191Labels = mixedMoment B node3434 node3434Labels := by
  calc
    mixedMoment B raw7191 raw7191Labels = mixedMoment B raw7191step0 raw7191step0Labels := by
      have ha : raw7191step0 = (fun i j => raw7191 (permutation673 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7191step0 raw7191; decide +kernel
      have hl : raw7191step0Labels = raw7191Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7191 raw7191Labels permutation673 permutation5
    mixedMoment B raw7191step0 raw7191step0Labels = mixedMoment B raw7191step1 raw7191step1Labels := by
      have ha : raw7191step1 = raw7191step0 := by apply Matrix.ext; unfold raw7191step1 raw7191step0; decide +kernel
      have hl : raw7191step0Labels = labelEmbedding1 ∘ raw7191step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7191step0 raw7191step0Labels raw7191step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3434 node3434Labels := by rfl

def raw7192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw7192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw7192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7192 raw7192Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw7192 raw7192Labels = mixedMoment B raw7192step0 raw7192step0Labels := by
      have hz : ∀ j, raw7192 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7192step0 = (fun i j => raw7192 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7192step0 raw7192; decide +kernel
      have hl : raw7192step0Labels = raw7192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7192 raw7192Labels permutation520 hz
    mixedMoment B raw7192step0 raw7192step0Labels = mixedMoment B raw7192step1 raw7192step1Labels := by
      have ha : raw7192step1 = (fun i j => raw7192step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7192step1 raw7192step0; decide +kernel
      have hl : raw7192step1Labels = raw7192step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7192step0 raw7192step0Labels permutation137 permutation5
    mixedMoment B raw7192step1 raw7192step1Labels = mixedMoment B raw7192step2 raw7192step2Labels := by
      have ha : raw7192step2 = raw7192step1 := by apply Matrix.ext; unfold raw7192step2 raw7192step1; decide +kernel
      have hl : raw7192step1Labels = labelEmbedding1 ∘ raw7192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7192step1 raw7192step1Labels raw7192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw7193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7193 raw7193Labels = mixedMoment B node2709 node2709Labels := by
  calc
    _ = mixedMoment B node2709 node2709Labels := by rfl

def raw7194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7194 raw7194Labels = mixedMoment B node3800 node3800Labels := by
  calc
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw7195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7195 raw7195Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw7195 raw7195Labels = mixedMoment B raw7195step0 raw7195step0Labels := by
      have ha : raw7195step0 = (fun i j => raw7195 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7195step0 raw7195; decide +kernel
      have hl : raw7195step0Labels = raw7195Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7195 raw7195Labels permutation176 permutation2
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw7196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7196 raw7196Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw7196 raw7196Labels = mixedMoment B raw7196step0 raw7196step0Labels := by
      have ha : raw7196step0 = (fun i j => raw7196 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7196step0 raw7196; decide +kernel
      have hl : raw7196step0Labels = raw7196Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7196 raw7196Labels permutation200 permutation2
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw7197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7197 raw7197Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw7197 raw7197Labels = mixedMoment B raw7197step0 raw7197step0Labels := by
      have hz : ∀ j, raw7197 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7197step0 = (fun i j => raw7197 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7197step0 raw7197; decide +kernel
      have hl : raw7197step0Labels = raw7197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7197 raw7197Labels permutation520 hz
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw7198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7198 raw7198Labels = mixedMoment B node3901 node3901Labels := by
  calc
    _ = mixedMoment B node3901 node3901Labels := by rfl

def raw7199 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw7199Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7199step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw7199step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical7199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7199 raw7199Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw7199 raw7199Labels = mixedMoment B raw7199step0 raw7199step0Labels := by
      have hz : ∀ j, raw7199 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7199step0 = (fun i j => raw7199 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7199step0 raw7199; decide +kernel
      have hl : raw7199step0Labels = raw7199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7199 raw7199Labels permutation520 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw7200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7200 raw7200Labels = mixedMoment B node1247 node1247Labels := by
  calc
    mixedMoment B raw7200 raw7200Labels = mixedMoment B raw7200step0 raw7200step0Labels := by
      have ha : raw7200step0 = (fun i j => raw7200 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7200step0 raw7200; decide +kernel
      have hl : raw7200step0Labels = raw7200Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7200 raw7200Labels permutation182 permutation2
    _ = mixedMoment B node1247 node1247Labels := by rfl

def raw7201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7201 raw7201Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw7201 raw7201Labels = mixedMoment B raw7201step0 raw7201step0Labels := by
      have ha : raw7201step0 = (fun i j => raw7201 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7201step0 raw7201; decide +kernel
      have hl : raw7201step0Labels = raw7201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7201 raw7201Labels permutation160 permutation2
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw7202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7202 raw7202Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw7202 raw7202Labels = mixedMoment B raw7202step0 raw7202step0Labels := by
      have ha : raw7202step0 = (fun i j => raw7202 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7202step0 raw7202; decide +kernel
      have hl : raw7202step0Labels = raw7202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7202 raw7202Labels permutation154 permutation2
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw7203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7203 raw7203Labels = mixedMoment B node1208 node1208Labels := by
  calc
    _ = mixedMoment B node1208 node1208Labels := by rfl

def raw7204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7204 raw7204Labels = mixedMoment B node1206 node1206Labels := by
  calc
    _ = mixedMoment B node1206 node1206Labels := by rfl

def raw7205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7205 raw7205Labels = mixedMoment B node2622 node2622Labels := by
  calc
    mixedMoment B raw7205 raw7205Labels = mixedMoment B raw7205step0 raw7205step0Labels := by
      have ha : raw7205step0 = (fun i j => raw7205 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7205step0 raw7205; decide +kernel
      have hl : raw7205step0Labels = raw7205Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7205 raw7205Labels permutation182 permutation2
    _ = mixedMoment B node2622 node2622Labels := by rfl

def raw7206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7206 raw7206Labels = mixedMoment B node2622 node2622Labels := by
  calc
    mixedMoment B raw7206 raw7206Labels = mixedMoment B raw7206step0 raw7206step0Labels := by
      have ha : raw7206step0 = (fun i j => raw7206 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7206step0 raw7206; decide +kernel
      have hl : raw7206step0Labels = raw7206Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7206 raw7206Labels permutation206 permutation2
    _ = mixedMoment B node2622 node2622Labels := by rfl

def raw7207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7207step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7207 raw7207Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw7207 raw7207Labels = mixedMoment B raw7207step0 raw7207step0Labels := by
      have hz : ∀ j, raw7207 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7207step0 = (fun i j => raw7207 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7207step0 raw7207; decide +kernel
      have hl : raw7207step0Labels = raw7207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7207 raw7207Labels permutation520 hz
    mixedMoment B raw7207step0 raw7207step0Labels = mixedMoment B raw7207step1 raw7207step1Labels := by
      have ha : raw7207step1 = (fun i j => raw7207step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7207step1 raw7207step0; decide +kernel
      have hl : raw7207step1Labels = raw7207step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7207step0 raw7207step0Labels permutation40 permutation2
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw7208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7208 raw7208Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw7208 raw7208Labels = mixedMoment B raw7208step0 raw7208step0Labels := by
      have ha : raw7208step0 = (fun i j => raw7208 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7208step0 raw7208; decide +kernel
      have hl : raw7208step0Labels = raw7208Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7208 raw7208Labels permutation182 permutation2
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw7209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7209 raw7209Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw7209 raw7209Labels = mixedMoment B raw7209step0 raw7209step0Labels := by
      have ha : raw7209step0 = (fun i j => raw7209 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7209step0 raw7209; decide +kernel
      have hl : raw7209step0Labels = raw7209Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7209 raw7209Labels permutation160 permutation2
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw7210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7210 raw7210Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw7210 raw7210Labels = mixedMoment B raw7210step0 raw7210step0Labels := by
      have ha : raw7210step0 = (fun i j => raw7210 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7210step0 raw7210; decide +kernel
      have hl : raw7210step0Labels = raw7210Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7210 raw7210Labels permutation154 permutation2
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw7211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7211 raw7211Labels = mixedMoment B node2473 node2473Labels := by
  calc
    _ = mixedMoment B node2473 node2473Labels := by rfl

def raw7212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7212 raw7212Labels = mixedMoment B node2470 node2470Labels := by
  calc
    _ = mixedMoment B node2470 node2470Labels := by rfl

def raw7213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7213 raw7213Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw7213 raw7213Labels = mixedMoment B raw7213step0 raw7213step0Labels := by
      have ha : raw7213step0 = (fun i j => raw7213 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7213step0 raw7213; decide +kernel
      have hl : raw7213step0Labels = raw7213Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7213 raw7213Labels permutation202 permutation2
    _ = mixedMoment B node2615 node2615Labels := by rfl

def raw7214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7214 raw7214Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw7214 raw7214Labels = mixedMoment B raw7214step0 raw7214step0Labels := by
      have hz : ∀ j, raw7214 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7214step0 = (fun i j => raw7214 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7214step0 raw7214; decide +kernel
      have hl : raw7214step0Labels = raw7214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7214 raw7214Labels permutation520 hz
    mixedMoment B raw7214step0 raw7214step0Labels = mixedMoment B raw7214step1 raw7214step1Labels := by
      have ha : raw7214step1 = (fun i j => raw7214step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7214step1 raw7214step0; decide +kernel
      have hl : raw7214step1Labels = raw7214step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7214step0 raw7214step0Labels permutation34 permutation2
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw7215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7215 raw7215Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw7215 raw7215Labels = mixedMoment B raw7215step0 raw7215step0Labels := by
      have ha : raw7215step0 = (fun i j => raw7215 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7215step0 raw7215; decide +kernel
      have hl : raw7215step0Labels = raw7215Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7215 raw7215Labels permutation160 permutation2
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw7216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7216 raw7216Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw7216 raw7216Labels = mixedMoment B raw7216step0 raw7216step0Labels := by
      have ha : raw7216step0 = (fun i j => raw7216 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7216step0 raw7216; decide +kernel
      have hl : raw7216step0Labels = raw7216Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7216 raw7216Labels permutation178 permutation2
    _ = mixedMoment B node2615 node2615Labels := by rfl

def raw7217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7217 raw7217Labels = mixedMoment B node2612 node2612Labels := by
  calc
    mixedMoment B raw7217 raw7217Labels = mixedMoment B raw7217step0 raw7217step0Labels := by
      have ha : raw7217step0 = (fun i j => raw7217 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7217step0 raw7217; decide +kernel
      have hl : raw7217step0Labels = raw7217Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7217 raw7217Labels permutation176 permutation2
    _ = mixedMoment B node2612 node2612Labels := by rfl

def raw7218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7218 raw7218Labels = mixedMoment B node2610 node2610Labels := by
  calc
    mixedMoment B raw7218 raw7218Labels = mixedMoment B raw7218step0 raw7218step0Labels := by
      have ha : raw7218step0 = (fun i j => raw7218 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7218step0 raw7218; decide +kernel
      have hl : raw7218step0Labels = raw7218Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7218 raw7218Labels permutation176 permutation2
    _ = mixedMoment B node2610 node2610Labels := by rfl

def raw7219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7219 raw7219Labels = mixedMoment B node2612 node2612Labels := by
  calc
    mixedMoment B raw7219 raw7219Labels = mixedMoment B raw7219step0 raw7219step0Labels := by
      have ha : raw7219step0 = (fun i j => raw7219 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7219step0 raw7219; decide +kernel
      have hl : raw7219step0Labels = raw7219Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7219 raw7219Labels permutation200 permutation2
    _ = mixedMoment B node2612 node2612Labels := by rfl

def raw7220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7220 raw7220Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw7220 raw7220Labels = mixedMoment B raw7220step0 raw7220step0Labels := by
      have ha : raw7220step0 = (fun i j => raw7220 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7220step0 raw7220; decide +kernel
      have hl : raw7220step0Labels = raw7220Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7220 raw7220Labels permutation153 permutation2
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw7221 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7221step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7221step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7221 raw7221Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw7221 raw7221Labels = mixedMoment B raw7221step0 raw7221step0Labels := by
      have ha : raw7221step0 = (fun i j => raw7221 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7221step0 raw7221; decide +kernel
      have hl : raw7221step0Labels = raw7221Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7221 raw7221Labels permutation182 permutation7
    mixedMoment B raw7221step0 raw7221step0Labels = mixedMoment B raw7221step1 raw7221step1Labels := by
      have ha : raw7221step1 = raw7221step0 := by apply Matrix.ext; unfold raw7221step1 raw7221step0; decide +kernel
      have hl : raw7221step0Labels = labelEmbedding10 ∘ raw7221step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7221step0 raw7221step0Labels raw7221step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

def raw7222 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7222step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7222step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7222 raw7222Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw7222 raw7222Labels = mixedMoment B raw7222step0 raw7222step0Labels := by
      have hz : ∀ j, raw7222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7222step0 = (fun i j => raw7222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7222step0 raw7222; decide +kernel
      have hl : raw7222step0Labels = raw7222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7222 raw7222Labels permutation434 hz
    mixedMoment B raw7222step0 raw7222step0Labels = mixedMoment B raw7222step1 raw7222step1Labels := by
      have ha : raw7222step1 = (fun i j => raw7222step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7222step1 raw7222step0; decide +kernel
      have hl : raw7222step1Labels = raw7222step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7222step0 raw7222step0Labels permutation38 permutation7
    mixedMoment B raw7222step1 raw7222step1Labels = mixedMoment B raw7222step2 raw7222step2Labels := by
      have ha : raw7222step2 = raw7222step1 := by apply Matrix.ext; unfold raw7222step2 raw7222step1; decide +kernel
      have hl : raw7222step1Labels = labelEmbedding10 ∘ raw7222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7222step1 raw7222step1Labels raw7222step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw7223 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7223step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7223step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7223 raw7223Labels = mixedMoment B node5242 node5242Labels := by
  calc
    mixedMoment B raw7223 raw7223Labels = mixedMoment B raw7223step0 raw7223step0Labels := by
      have ha : raw7223step0 = (fun i j => raw7223 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7223step0 raw7223; decide +kernel
      have hl : raw7223step0Labels = raw7223Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7223 raw7223Labels permutation182 permutation7
    mixedMoment B raw7223step0 raw7223step0Labels = mixedMoment B raw7223step1 raw7223step1Labels := by
      have ha : raw7223step1 = raw7223step0 := by apply Matrix.ext; unfold raw7223step1 raw7223step0; decide +kernel
      have hl : raw7223step0Labels = labelEmbedding10 ∘ raw7223step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7223step0 raw7223step0Labels raw7223step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5242 node5242Labels := by rfl

def raw7224 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw7224step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw7224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7224 raw7224Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw7224 raw7224Labels = mixedMoment B raw7224step0 raw7224step0Labels := by
      have ha : raw7224step0 = (fun i j => raw7224 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7224step0 raw7224; decide +kernel
      have hl : raw7224step0Labels = raw7224Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7224 raw7224Labels permutation182 permutation7
    mixedMoment B raw7224step0 raw7224step0Labels = mixedMoment B raw7224step1 raw7224step1Labels := by
      have ha : raw7224step1 = raw7224step0 := by apply Matrix.ext; unfold raw7224step1 raw7224step0; decide +kernel
      have hl : raw7224step0Labels = labelEmbedding10 ∘ raw7224step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7224step0 raw7224step0Labels raw7224step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw7225 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7225step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7225step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7225 raw7225Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw7225 raw7225Labels = mixedMoment B raw7225step0 raw7225step0Labels := by
      have hz : ∀ j, raw7225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7225step0 = (fun i j => raw7225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7225step0 raw7225; decide +kernel
      have hl : raw7225step0Labels = raw7225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7225 raw7225Labels permutation434 hz
    mixedMoment B raw7225step0 raw7225step0Labels = mixedMoment B raw7225step1 raw7225step1Labels := by
      have hz : ∀ j, raw7225step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7225step1 = (fun i j => raw7225step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7225step1 raw7225step0; decide +kernel
      have hl : raw7225step1Labels = raw7225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7225step0 raw7225step0Labels permutation56 hz
    mixedMoment B raw7225step1 raw7225step1Labels = mixedMoment B raw7225step2 raw7225step2Labels := by
      have ha : raw7225step2 = (fun i j => raw7225step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7225step2 raw7225step1; decide +kernel
      have hl : raw7225step2Labels = raw7225step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7225step1 raw7225step1Labels permutation8 permutation6
    mixedMoment B raw7225step2 raw7225step2Labels = mixedMoment B raw7225step3 raw7225step3Labels := by
      have ha : raw7225step3 = raw7225step2 := by apply Matrix.ext; unfold raw7225step3 raw7225step2; decide +kernel
      have hl : raw7225step2Labels = labelEmbedding9 ∘ raw7225step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7225step2 raw7225step2Labels raw7225step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw7226 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7226step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7226step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7226 raw7226Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw7226 raw7226Labels = mixedMoment B raw7226step0 raw7226step0Labels := by
      have hz : ∀ j, raw7226 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7226step0 = (fun i j => raw7226 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7226step0 raw7226; decide +kernel
      have hl : raw7226step0Labels = raw7226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7226 raw7226Labels permutation265 hz
    mixedMoment B raw7226step0 raw7226step0Labels = mixedMoment B raw7226step1 raw7226step1Labels := by
      have ha : raw7226step1 = (fun i j => raw7226step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7226step1 raw7226step0; decide +kernel
      have hl : raw7226step1Labels = raw7226step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7226step0 raw7226step0Labels permutation32 permutation6
    mixedMoment B raw7226step1 raw7226step1Labels = mixedMoment B raw7226step2 raw7226step2Labels := by
      have ha : raw7226step2 = raw7226step1 := by apply Matrix.ext; unfold raw7226step2 raw7226step1; decide +kernel
      have hl : raw7226step1Labels = labelEmbedding9 ∘ raw7226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7226step1 raw7226step1Labels raw7226step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw7227 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw7227step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7227step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7227step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7227 raw7227Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw7227 raw7227Labels = mixedMoment B raw7227step0 raw7227step0Labels := by
      have ha : raw7227step0 = (fun i j => raw7227 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7227step0 raw7227; decide +kernel
      have hl : raw7227step0Labels = raw7227Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7227 raw7227Labels permutation167 permutation4
    mixedMoment B raw7227step0 raw7227step0Labels = mixedMoment B raw7227step1 raw7227step1Labels := by
      have ha : raw7227step1 = -raw7227step0 := by apply Matrix.ext; change ∀ i j, raw7227step1 i j = -(raw7227step0 i j); unfold raw7227step1 raw7227step0; decide +kernel
      have hl : raw7227step1Labels = raw7227step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7227step1 raw7227step1Labels = mixedMoment B raw7227step2 raw7227step2Labels := by
      have ha : raw7227step2 = raw7227step1 := by apply Matrix.ext; unfold raw7227step2 raw7227step1; decide +kernel
      have hl : raw7227step1Labels = labelEmbedding7 ∘ raw7227step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7227step1 raw7227step1Labels raw7227step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw7228 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7228step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7228 raw7228Labels = mixedMoment B node5223 node5223Labels := by
  calc
    mixedMoment B raw7228 raw7228Labels = mixedMoment B raw7228step0 raw7228step0Labels := by
      have ha : raw7228step0 = (fun i j => raw7228 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7228step0 raw7228; decide +kernel
      have hl : raw7228step0Labels = raw7228Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7228 raw7228Labels permutation158 permutation6
    mixedMoment B raw7228step0 raw7228step0Labels = mixedMoment B raw7228step1 raw7228step1Labels := by
      have ha : raw7228step1 = raw7228step0 := by apply Matrix.ext; unfold raw7228step1 raw7228step0; decide +kernel
      have hl : raw7228step0Labels = labelEmbedding9 ∘ raw7228step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7228step0 raw7228step0Labels raw7228step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5223 node5223Labels := by rfl

def raw7229 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7229step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7229 raw7229Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw7229 raw7229Labels = mixedMoment B raw7229step0 raw7229step0Labels := by
      have hz : ∀ j, raw7229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7229step0 = (fun i j => raw7229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7229step0 raw7229; decide +kernel
      have hl : raw7229step0Labels = raw7229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7229 raw7229Labels permutation434 hz
    mixedMoment B raw7229step0 raw7229step0Labels = mixedMoment B raw7229step1 raw7229step1Labels := by
      have ha : raw7229step1 = (fun i j => raw7229step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7229step1 raw7229step0; decide +kernel
      have hl : raw7229step1Labels = raw7229step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7229step0 raw7229step0Labels permutation32 permutation6
    mixedMoment B raw7229step1 raw7229step1Labels = mixedMoment B raw7229step2 raw7229step2Labels := by
      have ha : raw7229step2 = raw7229step1 := by apply Matrix.ext; unfold raw7229step2 raw7229step1; decide +kernel
      have hl : raw7229step1Labels = labelEmbedding9 ∘ raw7229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7229step1 raw7229step1Labels raw7229step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw7230 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw7230step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw7230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7230 raw7230Labels = mixedMoment B node5253 node5253Labels := by
  calc
    mixedMoment B raw7230 raw7230Labels = mixedMoment B raw7230step0 raw7230step0Labels := by
      have ha : raw7230step0 = (fun i j => raw7230 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7230step0 raw7230; decide +kernel
      have hl : raw7230step0Labels = raw7230Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7230 raw7230Labels permutation158 permutation6
    mixedMoment B raw7230step0 raw7230step0Labels = mixedMoment B raw7230step1 raw7230step1Labels := by
      have ha : raw7230step1 = raw7230step0 := by apply Matrix.ext; unfold raw7230step1 raw7230step0; decide +kernel
      have hl : raw7230step0Labels = labelEmbedding9 ∘ raw7230step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7230step0 raw7230step0Labels raw7230step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5253 node5253Labels := by rfl

def raw7231 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw7231step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw7231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7231 raw7231Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw7231 raw7231Labels = mixedMoment B raw7231step0 raw7231step0Labels := by
      have ha : raw7231step0 = (fun i j => raw7231 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7231step0 raw7231; decide +kernel
      have hl : raw7231step0Labels = raw7231Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7231 raw7231Labels permutation158 permutation6
    mixedMoment B raw7231step0 raw7231step0Labels = mixedMoment B raw7231step1 raw7231step1Labels := by
      have ha : raw7231step1 = raw7231step0 := by apply Matrix.ext; unfold raw7231step1 raw7231step0; decide +kernel
      have hl : raw7231step0Labels = labelEmbedding9 ∘ raw7231step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7231step0 raw7231step0Labels raw7231step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw7232 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7232step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7232step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7232step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7232step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7232 raw7232Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw7232 raw7232Labels = mixedMoment B raw7232step0 raw7232step0Labels := by
      have ha : raw7232step0 = (fun i j => raw7232 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7232step0 raw7232; decide +kernel
      have hl : raw7232step0Labels = raw7232Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7232 raw7232Labels permutation152 permutation4
    mixedMoment B raw7232step0 raw7232step0Labels = mixedMoment B raw7232step1 raw7232step1Labels := by
      have ha : raw7232step1 = -raw7232step0 := by apply Matrix.ext; change ∀ i j, raw7232step1 i j = -(raw7232step0 i j); unfold raw7232step1 raw7232step0; decide +kernel
      have hl : raw7232step1Labels = raw7232step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7232step1 raw7232step1Labels = mixedMoment B raw7232step2 raw7232step2Labels := by
      have ha : raw7232step2 = raw7232step1 := by apply Matrix.ext; unfold raw7232step2 raw7232step1; decide +kernel
      have hl : raw7232step1Labels = labelEmbedding7 ∘ raw7232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7232step1 raw7232step1Labels raw7232step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw7233 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7233step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7233 raw7233Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw7233 raw7233Labels = mixedMoment B raw7233step0 raw7233step0Labels := by
      have ha : raw7233step0 = (fun i j => raw7233 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7233step0 raw7233; decide +kernel
      have hl : raw7233step0Labels = raw7233Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7233 raw7233Labels permutation152 permutation6
    mixedMoment B raw7233step0 raw7233step0Labels = mixedMoment B raw7233step1 raw7233step1Labels := by
      have ha : raw7233step1 = raw7233step0 := by apply Matrix.ext; unfold raw7233step1 raw7233step0; decide +kernel
      have hl : raw7233step0Labels = labelEmbedding9 ∘ raw7233step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7233step0 raw7233step0Labels raw7233step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

def raw7234 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7234step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7234step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7234 raw7234Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw7234 raw7234Labels = mixedMoment B raw7234step0 raw7234step0Labels := by
      have hz : ∀ j, raw7234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7234step0 = (fun i j => raw7234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7234step0 raw7234; decide +kernel
      have hl : raw7234step0Labels = raw7234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7234 raw7234Labels permutation434 hz
    mixedMoment B raw7234step0 raw7234step0Labels = mixedMoment B raw7234step1 raw7234step1Labels := by
      have ha : raw7234step1 = (fun i j => raw7234step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7234step1 raw7234step0; decide +kernel
      have hl : raw7234step1Labels = raw7234step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7234step0 raw7234step0Labels permutation32 permutation6
    mixedMoment B raw7234step1 raw7234step1Labels = mixedMoment B raw7234step2 raw7234step2Labels := by
      have ha : raw7234step2 = raw7234step1 := by apply Matrix.ext; unfold raw7234step2 raw7234step1; decide +kernel
      have hl : raw7234step1Labels = labelEmbedding9 ∘ raw7234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7234step1 raw7234step1Labels raw7234step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw7235 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7235step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7235step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7235step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7235step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7235 raw7235Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw7235 raw7235Labels = mixedMoment B raw7235step0 raw7235step0Labels := by
      have ha : raw7235step0 = (fun i j => raw7235 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7235step0 raw7235; decide +kernel
      have hl : raw7235step0Labels = raw7235Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7235 raw7235Labels permutation164 permutation4
    mixedMoment B raw7235step0 raw7235step0Labels = mixedMoment B raw7235step1 raw7235step1Labels := by
      have ha : raw7235step1 = -raw7235step0 := by apply Matrix.ext; change ∀ i j, raw7235step1 i j = -(raw7235step0 i j); unfold raw7235step1 raw7235step0; decide +kernel
      have hl : raw7235step1Labels = raw7235step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7235step1 raw7235step1Labels = mixedMoment B raw7235step2 raw7235step2Labels := by
      have ha : raw7235step2 = raw7235step1 := by apply Matrix.ext; unfold raw7235step2 raw7235step1; decide +kernel
      have hl : raw7235step1Labels = labelEmbedding7 ∘ raw7235step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7235step1 raw7235step1Labels raw7235step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw7236 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7236step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7236 raw7236Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw7236 raw7236Labels = mixedMoment B raw7236step0 raw7236step0Labels := by
      have ha : raw7236step0 = (fun i j => raw7236 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7236step0 raw7236; decide +kernel
      have hl : raw7236step0Labels = raw7236Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7236 raw7236Labels permutation152 permutation6
    mixedMoment B raw7236step0 raw7236step0Labels = mixedMoment B raw7236step1 raw7236step1Labels := by
      have ha : raw7236step1 = raw7236step0 := by apply Matrix.ext; unfold raw7236step1 raw7236step0; decide +kernel
      have hl : raw7236step0Labels = labelEmbedding9 ∘ raw7236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7236step0 raw7236step0Labels raw7236step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw7237 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7237step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7237 raw7237Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw7237 raw7237Labels = mixedMoment B raw7237step0 raw7237step0Labels := by
      have hz : ∀ j, raw7237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7237step0 = (fun i j => raw7237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7237step0 raw7237; decide +kernel
      have hl : raw7237step0Labels = raw7237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7237 raw7237Labels permutation434 hz
    mixedMoment B raw7237step0 raw7237step0Labels = mixedMoment B raw7237step1 raw7237step1Labels := by
      have ha : raw7237step1 = (fun i j => raw7237step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7237step1 raw7237step0; decide +kernel
      have hl : raw7237step1Labels = raw7237step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7237step0 raw7237step0Labels permutation32 permutation6
    mixedMoment B raw7237step1 raw7237step1Labels = mixedMoment B raw7237step2 raw7237step2Labels := by
      have ha : raw7237step2 = raw7237step1 := by apply Matrix.ext; unfold raw7237step2 raw7237step1; decide +kernel
      have hl : raw7237step1Labels = labelEmbedding9 ∘ raw7237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7237step1 raw7237step1Labels raw7237step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw7238 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7238step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7238 raw7238Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw7238 raw7238Labels = mixedMoment B raw7238step0 raw7238step0Labels := by
      have ha : raw7238step0 = (fun i j => raw7238 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7238step0 raw7238; decide +kernel
      have hl : raw7238step0Labels = raw7238Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7238 raw7238Labels permutation152 permutation6
    mixedMoment B raw7238step0 raw7238step0Labels = mixedMoment B raw7238step1 raw7238step1Labels := by
      have ha : raw7238step1 = raw7238step0 := by apply Matrix.ext; unfold raw7238step1 raw7238step0; decide +kernel
      have hl : raw7238step0Labels = labelEmbedding9 ∘ raw7238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7238step0 raw7238step0Labels raw7238step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw7239 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7239 raw7239Labels = mixedMoment B node3029 node3029Labels := by
  calc
    mixedMoment B raw7239 raw7239Labels = mixedMoment B raw7239step0 raw7239step0Labels := by
      have ha : raw7239step0 = (fun i j => raw7239 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7239step0 raw7239; decide +kernel
      have hl : raw7239step0Labels = raw7239Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7239 raw7239Labels permutation152 permutation6
    _ = mixedMoment B node3029 node3029Labels := by rfl

def raw7240 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7240 raw7240Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw7240 raw7240Labels = mixedMoment B raw7240step0 raw7240step0Labels := by
      have hz : ∀ j, raw7240 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7240step0 = (fun i j => raw7240 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7240step0 raw7240; decide +kernel
      have hl : raw7240step0Labels = raw7240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7240 raw7240Labels permutation434 hz
    mixedMoment B raw7240step0 raw7240step0Labels = mixedMoment B raw7240step1 raw7240step1Labels := by
      have ha : raw7240step1 = (fun i j => raw7240step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7240step1 raw7240step0; decide +kernel
      have hl : raw7240step1Labels = raw7240step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7240step0 raw7240step0Labels permutation32 permutation6
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw7241 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7241 raw7241Labels = mixedMoment B node3080 node3080Labels := by
  calc
    mixedMoment B raw7241 raw7241Labels = mixedMoment B raw7241step0 raw7241step0Labels := by
      have ha : raw7241step0 = (fun i j => raw7241 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7241step0 raw7241; decide +kernel
      have hl : raw7241step0Labels = raw7241Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7241 raw7241Labels permutation152 permutation6
    _ = mixedMoment B node3080 node3080Labels := by rfl

def raw7242 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw7242step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7242 raw7242Labels = mixedMoment B node3081 node3081Labels := by
  calc
    mixedMoment B raw7242 raw7242Labels = mixedMoment B raw7242step0 raw7242step0Labels := by
      have ha : raw7242step0 = (fun i j => raw7242 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7242step0 raw7242; decide +kernel
      have hl : raw7242step0Labels = raw7242Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7242 raw7242Labels permutation152 permutation6
    _ = mixedMoment B node3081 node3081Labels := by rfl

def raw7243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7243step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7243step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7243 raw7243Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw7243 raw7243Labels = mixedMoment B raw7243step0 raw7243step0Labels := by
      have hz : ∀ j, raw7243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7243step0 = (fun i j => raw7243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7243step0 raw7243; decide +kernel
      have hl : raw7243step0Labels = raw7243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7243 raw7243Labels permutation434 hz
    mixedMoment B raw7243step0 raw7243step0Labels = mixedMoment B raw7243step1 raw7243step1Labels := by
      have hz : ∀ j, raw7243step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7243step1 = (fun i j => raw7243step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7243step1 raw7243step0; decide +kernel
      have hl : raw7243step1Labels = raw7243step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7243step0 raw7243step0Labels permutation56 hz
    mixedMoment B raw7243step1 raw7243step1Labels = mixedMoment B raw7243step2 raw7243step2Labels := by
      have ha : raw7243step2 = (fun i j => raw7243step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7243step2 raw7243step1; decide +kernel
      have hl : raw7243step2Labels = raw7243step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7243step1 raw7243step1Labels permutation8 permutation6
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw7244 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7244step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7244 raw7244Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw7244 raw7244Labels = mixedMoment B raw7244step0 raw7244step0Labels := by
      have hz : ∀ j, raw7244 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7244step0 = (fun i j => raw7244 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7244step0 raw7244; decide +kernel
      have hl : raw7244step0Labels = raw7244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7244 raw7244Labels permutation265 hz
    mixedMoment B raw7244step0 raw7244step0Labels = mixedMoment B raw7244step1 raw7244step1Labels := by
      have ha : raw7244step1 = (fun i j => raw7244step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7244step1 raw7244step0; decide +kernel
      have hl : raw7244step1Labels = raw7244step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7244step0 raw7244step0Labels permutation32 permutation6
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw7245 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7245 raw7245Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw7245 raw7245Labels = mixedMoment B raw7245step0 raw7245step0Labels := by
      have ha : raw7245step0 = (fun i j => raw7245 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7245step0 raw7245; decide +kernel
      have hl : raw7245step0Labels = raw7245Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7245 raw7245Labels permutation158 permutation6
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw7246 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7246step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7246 raw7246Labels = mixedMoment B node2665 node2665Labels := by
  calc
    mixedMoment B raw7246 raw7246Labels = mixedMoment B raw7246step0 raw7246step0Labels := by
      have ha : raw7246step0 = (fun i j => raw7246 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7246step0 raw7246; decide +kernel
      have hl : raw7246step0Labels = raw7246Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7246 raw7246Labels permutation158 permutation6
    _ = mixedMoment B node2665 node2665Labels := by rfl

def raw7247 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7247step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7247 raw7247Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw7247 raw7247Labels = mixedMoment B raw7247step0 raw7247step0Labels := by
      have hz : ∀ j, raw7247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7247step0 = (fun i j => raw7247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7247step0 raw7247; decide +kernel
      have hl : raw7247step0Labels = raw7247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7247 raw7247Labels permutation434 hz
    mixedMoment B raw7247step0 raw7247step0Labels = mixedMoment B raw7247step1 raw7247step1Labels := by
      have ha : raw7247step1 = (fun i j => raw7247step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7247step1 raw7247step0; decide +kernel
      have hl : raw7247step1Labels = raw7247step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7247step0 raw7247step0Labels permutation32 permutation6
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw7248 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw7248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7248 raw7248Labels = mixedMoment B node2713 node2713Labels := by
  calc
    mixedMoment B raw7248 raw7248Labels = mixedMoment B raw7248step0 raw7248step0Labels := by
      have ha : raw7248step0 = (fun i j => raw7248 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7248step0 raw7248; decide +kernel
      have hl : raw7248step0Labels = raw7248Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7248 raw7248Labels permutation158 permutation6
    _ = mixedMoment B node2713 node2713Labels := by rfl

def raw7249 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw7249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7249 raw7249Labels = mixedMoment B node2714 node2714Labels := by
  calc
    mixedMoment B raw7249 raw7249Labels = mixedMoment B raw7249step0 raw7249step0Labels := by
      have ha : raw7249step0 = (fun i j => raw7249 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7249step0 raw7249; decide +kernel
      have hl : raw7249step0Labels = raw7249Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7249 raw7249Labels permutation158 permutation6
    _ = mixedMoment B node2714 node2714Labels := by rfl

def raw7250 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7250step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7250 raw7250Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw7250 raw7250Labels = mixedMoment B raw7250step0 raw7250step0Labels := by
      have ha : raw7250step0 = (fun i j => raw7250 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7250step0 raw7250; decide +kernel
      have hl : raw7250step0Labels = raw7250Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7250 raw7250Labels permutation152 permutation6
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw7251 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7251 raw7251Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw7251 raw7251Labels = mixedMoment B raw7251step0 raw7251step0Labels := by
      have ha : raw7251step0 = (fun i j => raw7251 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7251step0 raw7251; decide +kernel
      have hl : raw7251step0Labels = raw7251Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7251 raw7251Labels permutation152 permutation6
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw7252 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7252 raw7252Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw7252 raw7252Labels = mixedMoment B raw7252step0 raw7252step0Labels := by
      have hz : ∀ j, raw7252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7252step0 = (fun i j => raw7252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7252step0 raw7252; decide +kernel
      have hl : raw7252step0Labels = raw7252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7252 raw7252Labels permutation434 hz
    mixedMoment B raw7252step0 raw7252step0Labels = mixedMoment B raw7252step1 raw7252step1Labels := by
      have ha : raw7252step1 = (fun i j => raw7252step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7252step1 raw7252step0; decide +kernel
      have hl : raw7252step1Labels = raw7252step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7252step0 raw7252step0Labels permutation32 permutation6
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw7253 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7253 raw7253Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw7253 raw7253Labels = mixedMoment B raw7253step0 raw7253step0Labels := by
      have ha : raw7253step0 = (fun i j => raw7253 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7253step0 raw7253; decide +kernel
      have hl : raw7253step0Labels = raw7253Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7253 raw7253Labels permutation152 permutation6
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw7254 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7254 raw7254Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw7254 raw7254Labels = mixedMoment B raw7254step0 raw7254step0Labels := by
      have ha : raw7254step0 = (fun i j => raw7254 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7254step0 raw7254; decide +kernel
      have hl : raw7254step0Labels = raw7254Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7254 raw7254Labels permutation152 permutation6
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw7255 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7255step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7255 raw7255Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw7255 raw7255Labels = mixedMoment B raw7255step0 raw7255step0Labels := by
      have hz : ∀ j, raw7255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7255step0 = (fun i j => raw7255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7255step0 raw7255; decide +kernel
      have hl : raw7255step0Labels = raw7255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7255 raw7255Labels permutation434 hz
    mixedMoment B raw7255step0 raw7255step0Labels = mixedMoment B raw7255step1 raw7255step1Labels := by
      have ha : raw7255step1 = (fun i j => raw7255step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7255step1 raw7255step0; decide +kernel
      have hl : raw7255step1Labels = raw7255step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7255step0 raw7255step0Labels permutation32 permutation6
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw7256 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7256 raw7256Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw7256 raw7256Labels = mixedMoment B raw7256step0 raw7256step0Labels := by
      have ha : raw7256step0 = (fun i j => raw7256 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7256step0 raw7256; decide +kernel
      have hl : raw7256step0Labels = raw7256Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7256 raw7256Labels permutation152 permutation6
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw7257 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7257Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7257step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7257 raw7257Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw7257 raw7257Labels = mixedMoment B raw7257step0 raw7257step0Labels := by
      have ha : raw7257step0 = (fun i j => raw7257 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7257step0 raw7257; decide +kernel
      have hl : raw7257step0Labels = raw7257Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7257 raw7257Labels permutation182 permutation7
    mixedMoment B raw7257step0 raw7257step0Labels = mixedMoment B raw7257step1 raw7257step1Labels := by
      have ha : raw7257step1 = raw7257step0 := by apply Matrix.ext; unfold raw7257step1 raw7257step0; decide +kernel
      have hl : raw7257step0Labels = labelEmbedding1 ∘ raw7257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7257step0 raw7257step0Labels raw7257step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2698 node2698Labels := by rfl

def raw7258 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7258step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7258step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7258 raw7258Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw7258 raw7258Labels = mixedMoment B raw7258step0 raw7258step0Labels := by
      have hz : ∀ j, raw7258 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7258step0 = (fun i j => raw7258 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7258step0 raw7258; decide +kernel
      have hl : raw7258step0Labels = raw7258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7258 raw7258Labels permutation434 hz
    mixedMoment B raw7258step0 raw7258step0Labels = mixedMoment B raw7258step1 raw7258step1Labels := by
      have ha : raw7258step1 = (fun i j => raw7258step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7258step1 raw7258step0; decide +kernel
      have hl : raw7258step1Labels = raw7258step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7258step0 raw7258step0Labels permutation38 permutation7
    mixedMoment B raw7258step1 raw7258step1Labels = mixedMoment B raw7258step2 raw7258step2Labels := by
      have ha : raw7258step2 = raw7258step1 := by apply Matrix.ext; unfold raw7258step2 raw7258step1; decide +kernel
      have hl : raw7258step1Labels = labelEmbedding1 ∘ raw7258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7258step1 raw7258step1Labels raw7258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw7259 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7259Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7259step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7259 raw7259Labels = mixedMoment B node2695 node2695Labels := by
  calc
    mixedMoment B raw7259 raw7259Labels = mixedMoment B raw7259step0 raw7259step0Labels := by
      have ha : raw7259step0 = (fun i j => raw7259 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7259step0 raw7259; decide +kernel
      have hl : raw7259step0Labels = raw7259Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7259 raw7259Labels permutation182 permutation7
    mixedMoment B raw7259step0 raw7259step0Labels = mixedMoment B raw7259step1 raw7259step1Labels := by
      have ha : raw7259step1 = raw7259step0 := by apply Matrix.ext; unfold raw7259step1 raw7259step0; decide +kernel
      have hl : raw7259step0Labels = labelEmbedding1 ∘ raw7259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7259step0 raw7259step0Labels raw7259step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2695 node2695Labels := by rfl

def raw7260 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw7260step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw7260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7260 raw7260Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw7260 raw7260Labels = mixedMoment B raw7260step0 raw7260step0Labels := by
      have ha : raw7260step0 = (fun i j => raw7260 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7260step0 raw7260; decide +kernel
      have hl : raw7260step0Labels = raw7260Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7260 raw7260Labels permutation182 permutation7
    mixedMoment B raw7260step0 raw7260step0Labels = mixedMoment B raw7260step1 raw7260step1Labels := by
      have ha : raw7260step1 = raw7260step0 := by apply Matrix.ext; unfold raw7260step1 raw7260step0; decide +kernel
      have hl : raw7260step0Labels = labelEmbedding1 ∘ raw7260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7260step0 raw7260step0Labels raw7260step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw7261 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7261Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7261step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7261step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7261step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7261step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7261step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7261 raw7261Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw7261 raw7261Labels = mixedMoment B raw7261step0 raw7261step0Labels := by
      have hz : ∀ j, raw7261 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7261step0 = (fun i j => raw7261 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7261step0 raw7261; decide +kernel
      have hl : raw7261step0Labels = raw7261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7261 raw7261Labels permutation434 hz
    mixedMoment B raw7261step0 raw7261step0Labels = mixedMoment B raw7261step1 raw7261step1Labels := by
      have hz : ∀ j, raw7261step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7261step1 = (fun i j => raw7261step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7261step1 raw7261step0; decide +kernel
      have hl : raw7261step1Labels = raw7261step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7261step0 raw7261step0Labels permutation56 hz
    mixedMoment B raw7261step1 raw7261step1Labels = mixedMoment B raw7261step2 raw7261step2Labels := by
      have ha : raw7261step2 = (fun i j => raw7261step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7261step2 raw7261step1; decide +kernel
      have hl : raw7261step2Labels = raw7261step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7261step1 raw7261step1Labels permutation8 permutation7
    mixedMoment B raw7261step2 raw7261step2Labels = mixedMoment B raw7261step3 raw7261step3Labels := by
      have ha : raw7261step3 = raw7261step2 := by apply Matrix.ext; unfold raw7261step3 raw7261step2; decide +kernel
      have hl : raw7261step2Labels = labelEmbedding1 ∘ raw7261step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7261step2 raw7261step2Labels raw7261step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw7262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7262step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7262 raw7262Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw7262 raw7262Labels = mixedMoment B raw7262step0 raw7262step0Labels := by
      have hz : ∀ j, raw7262 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7262step0 = (fun i j => raw7262 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7262step0 raw7262; decide +kernel
      have hl : raw7262step0Labels = raw7262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7262 raw7262Labels permutation265 hz
    mixedMoment B raw7262step0 raw7262step0Labels = mixedMoment B raw7262step1 raw7262step1Labels := by
      have ha : raw7262step1 = (fun i j => raw7262step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7262step1 raw7262step0; decide +kernel
      have hl : raw7262step1Labels = raw7262step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7262step0 raw7262step0Labels permutation32 permutation7
    mixedMoment B raw7262step1 raw7262step1Labels = mixedMoment B raw7262step2 raw7262step2Labels := by
      have ha : raw7262step2 = raw7262step1 := by apply Matrix.ext; unfold raw7262step2 raw7262step1; decide +kernel
      have hl : raw7262step1Labels = labelEmbedding1 ∘ raw7262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7262step1 raw7262step1Labels raw7262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw7263 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7263Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw7263step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7263step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7263step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7263step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7263 raw7263Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw7263 raw7263Labels = mixedMoment B raw7263step0 raw7263step0Labels := by
      have ha : raw7263step0 = (fun i j => raw7263 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7263step0 raw7263; decide +kernel
      have hl : raw7263step0Labels = raw7263Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7263 raw7263Labels permutation169 permutation5
    mixedMoment B raw7263step0 raw7263step0Labels = mixedMoment B raw7263step1 raw7263step1Labels := by
      have ha : raw7263step1 = -raw7263step0 := by apply Matrix.ext; change ∀ i j, raw7263step1 i j = -(raw7263step0 i j); unfold raw7263step1 raw7263step0; decide +kernel
      have hl : raw7263step1Labels = raw7263step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7263step1 raw7263step1Labels = mixedMoment B raw7263step2 raw7263step2Labels := by
      have ha : raw7263step2 = raw7263step1 := by apply Matrix.ext; unfold raw7263step2 raw7263step1; decide +kernel
      have hl : raw7263step1Labels = labelEmbedding1 ∘ raw7263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7263step1 raw7263step1Labels raw7263step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw7264 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7264Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7264step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7264 raw7264Labels = mixedMoment B node3019 node3019Labels := by
  calc
    mixedMoment B raw7264 raw7264Labels = mixedMoment B raw7264step0 raw7264step0Labels := by
      have ha : raw7264step0 = (fun i j => raw7264 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7264step0 raw7264; decide +kernel
      have hl : raw7264step0Labels = raw7264Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7264 raw7264Labels permutation182 permutation7
    mixedMoment B raw7264step0 raw7264step0Labels = mixedMoment B raw7264step1 raw7264step1Labels := by
      have ha : raw7264step1 = raw7264step0 := by apply Matrix.ext; unfold raw7264step1 raw7264step0; decide +kernel
      have hl : raw7264step0Labels = labelEmbedding1 ∘ raw7264step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7264step0 raw7264step0Labels raw7264step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3019 node3019Labels := by rfl

def raw7265 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7265Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7265step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7265step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7265 raw7265Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw7265 raw7265Labels = mixedMoment B raw7265step0 raw7265step0Labels := by
      have hz : ∀ j, raw7265 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7265step0 = (fun i j => raw7265 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7265step0 raw7265; decide +kernel
      have hl : raw7265step0Labels = raw7265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7265 raw7265Labels permutation434 hz
    mixedMoment B raw7265step0 raw7265step0Labels = mixedMoment B raw7265step1 raw7265step1Labels := by
      have ha : raw7265step1 = (fun i j => raw7265step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7265step1 raw7265step0; decide +kernel
      have hl : raw7265step1Labels = raw7265step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7265step0 raw7265step0Labels permutation38 permutation7
    mixedMoment B raw7265step1 raw7265step1Labels = mixedMoment B raw7265step2 raw7265step2Labels := by
      have ha : raw7265step2 = raw7265step1 := by apply Matrix.ext; unfold raw7265step2 raw7265step1; decide +kernel
      have hl : raw7265step1Labels = labelEmbedding1 ∘ raw7265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7265step1 raw7265step1Labels raw7265step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw7266 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7266Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7266step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7266 raw7266Labels = mixedMoment B node3017 node3017Labels := by
  calc
    mixedMoment B raw7266 raw7266Labels = mixedMoment B raw7266step0 raw7266step0Labels := by
      have ha : raw7266step0 = (fun i j => raw7266 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7266step0 raw7266; decide +kernel
      have hl : raw7266step0Labels = raw7266Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7266 raw7266Labels permutation182 permutation7
    mixedMoment B raw7266step0 raw7266step0Labels = mixedMoment B raw7266step1 raw7266step1Labels := by
      have ha : raw7266step1 = raw7266step0 := by apply Matrix.ext; unfold raw7266step1 raw7266step0; decide +kernel
      have hl : raw7266step0Labels = labelEmbedding1 ∘ raw7266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7266step0 raw7266step0Labels raw7266step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3017 node3017Labels := by rfl

def raw7267 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7267Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw7267step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw7267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7267 raw7267Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw7267 raw7267Labels = mixedMoment B raw7267step0 raw7267step0Labels := by
      have ha : raw7267step0 = (fun i j => raw7267 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7267step0 raw7267; decide +kernel
      have hl : raw7267step0Labels = raw7267Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7267 raw7267Labels permutation182 permutation7
    mixedMoment B raw7267step0 raw7267step0Labels = mixedMoment B raw7267step1 raw7267step1Labels := by
      have ha : raw7267step1 = raw7267step0 := by apply Matrix.ext; unfold raw7267step1 raw7267step0; decide +kernel
      have hl : raw7267step0Labels = labelEmbedding1 ∘ raw7267step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7267step0 raw7267step0Labels raw7267step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw7268 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7268Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7268step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7268step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7268step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7268 raw7268Labels = mixedMoment B node3209 node3209Labels := by
  calc
    mixedMoment B raw7268 raw7268Labels = mixedMoment B raw7268step0 raw7268step0Labels := by
      have ha : raw7268step0 = (fun i j => raw7268 (permutation174 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7268step0 raw7268; decide +kernel
      have hl : raw7268step0Labels = raw7268Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7268 raw7268Labels permutation174 permutation5
    mixedMoment B raw7268step0 raw7268step0Labels = mixedMoment B raw7268step1 raw7268step1Labels := by
      have ha : raw7268step1 = -raw7268step0 := by apply Matrix.ext; change ∀ i j, raw7268step1 i j = -(raw7268step0 i j); unfold raw7268step1 raw7268step0; decide +kernel
      have hl : raw7268step1Labels = raw7268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7268step1 raw7268step1Labels = mixedMoment B raw7268step2 raw7268step2Labels := by
      have ha : raw7268step2 = raw7268step1 := by apply Matrix.ext; unfold raw7268step2 raw7268step1; decide +kernel
      have hl : raw7268step1Labels = labelEmbedding1 ∘ raw7268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7268step1 raw7268step1Labels raw7268step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3209 node3209Labels := by rfl

def raw7269 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7269Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7269step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7269step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7269 raw7269Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw7269 raw7269Labels = mixedMoment B raw7269step0 raw7269step0Labels := by
      have ha : raw7269step0 = (fun i j => raw7269 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7269step0 raw7269; decide +kernel
      have hl : raw7269step0Labels = raw7269Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7269 raw7269Labels permutation182 permutation7
    mixedMoment B raw7269step0 raw7269step0Labels = mixedMoment B raw7269step1 raw7269step1Labels := by
      have ha : raw7269step1 = raw7269step0 := by apply Matrix.ext; unfold raw7269step1 raw7269step0; decide +kernel
      have hl : raw7269step0Labels = labelEmbedding1 ∘ raw7269step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7269step0 raw7269step0Labels raw7269step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3068 node3068Labels := by rfl

def raw7270 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7270step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7270step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7270 raw7270Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw7270 raw7270Labels = mixedMoment B raw7270step0 raw7270step0Labels := by
      have hz : ∀ j, raw7270 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7270step0 = (fun i j => raw7270 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7270step0 raw7270; decide +kernel
      have hl : raw7270step0Labels = raw7270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7270 raw7270Labels permutation434 hz
    mixedMoment B raw7270step0 raw7270step0Labels = mixedMoment B raw7270step1 raw7270step1Labels := by
      have ha : raw7270step1 = (fun i j => raw7270step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7270step1 raw7270step0; decide +kernel
      have hl : raw7270step1Labels = raw7270step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7270step0 raw7270step0Labels permutation38 permutation7
    mixedMoment B raw7270step1 raw7270step1Labels = mixedMoment B raw7270step2 raw7270step2Labels := by
      have ha : raw7270step2 = raw7270step1 := by apply Matrix.ext; unfold raw7270step2 raw7270step1; decide +kernel
      have hl : raw7270step1Labels = labelEmbedding1 ∘ raw7270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7270step1 raw7270step1Labels raw7270step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw7271 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7271Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7271step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7271 raw7271Labels = mixedMoment B node3205 node3205Labels := by
  calc
    mixedMoment B raw7271 raw7271Labels = mixedMoment B raw7271step0 raw7271step0Labels := by
      have ha : raw7271step0 = (fun i j => raw7271 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7271step0 raw7271; decide +kernel
      have hl : raw7271step0Labels = raw7271Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7271 raw7271Labels permutation164 permutation5
    mixedMoment B raw7271step0 raw7271step0Labels = mixedMoment B raw7271step1 raw7271step1Labels := by
      have ha : raw7271step1 = -raw7271step0 := by apply Matrix.ext; change ∀ i j, raw7271step1 i j = -(raw7271step0 i j); unfold raw7271step1 raw7271step0; decide +kernel
      have hl : raw7271step1Labels = raw7271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7271step1 raw7271step1Labels = mixedMoment B raw7271step2 raw7271step2Labels := by
      have ha : raw7271step2 = raw7271step1 := by apply Matrix.ext; unfold raw7271step2 raw7271step1; decide +kernel
      have hl : raw7271step1Labels = labelEmbedding1 ∘ raw7271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7271step1 raw7271step1Labels raw7271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3205 node3205Labels := by rfl

def raw7272 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7272step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7272 raw7272Labels = mixedMoment B node3069 node3069Labels := by
  calc
    mixedMoment B raw7272 raw7272Labels = mixedMoment B raw7272step0 raw7272step0Labels := by
      have ha : raw7272step0 = (fun i j => raw7272 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7272step0 raw7272; decide +kernel
      have hl : raw7272step0Labels = raw7272Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7272 raw7272Labels permutation182 permutation7
    mixedMoment B raw7272step0 raw7272step0Labels = mixedMoment B raw7272step1 raw7272step1Labels := by
      have ha : raw7272step1 = raw7272step0 := by apply Matrix.ext; unfold raw7272step1 raw7272step0; decide +kernel
      have hl : raw7272step0Labels = labelEmbedding1 ∘ raw7272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7272step0 raw7272step0Labels raw7272step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3069 node3069Labels := by rfl

def raw7273 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7273Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7273step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7273 raw7273Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw7273 raw7273Labels = mixedMoment B raw7273step0 raw7273step0Labels := by
      have hz : ∀ j, raw7273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7273step0 = (fun i j => raw7273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7273step0 raw7273; decide +kernel
      have hl : raw7273step0Labels = raw7273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7273 raw7273Labels permutation434 hz
    mixedMoment B raw7273step0 raw7273step0Labels = mixedMoment B raw7273step1 raw7273step1Labels := by
      have ha : raw7273step1 = (fun i j => raw7273step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7273step1 raw7273step0; decide +kernel
      have hl : raw7273step1Labels = raw7273step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7273step0 raw7273step0Labels permutation38 permutation7
    mixedMoment B raw7273step1 raw7273step1Labels = mixedMoment B raw7273step2 raw7273step2Labels := by
      have ha : raw7273step2 = raw7273step1 := by apply Matrix.ext; unfold raw7273step2 raw7273step1; decide +kernel
      have hl : raw7273step1Labels = labelEmbedding1 ∘ raw7273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7273step1 raw7273step1Labels raw7273step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw7274 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7274Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7274step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7274 raw7274Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw7274 raw7274Labels = mixedMoment B raw7274step0 raw7274step0Labels := by
      have ha : raw7274step0 = (fun i j => raw7274 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7274step0 raw7274; decide +kernel
      have hl : raw7274step0Labels = raw7274Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7274 raw7274Labels permutation182 permutation7
    mixedMoment B raw7274step0 raw7274step0Labels = mixedMoment B raw7274step1 raw7274step1Labels := by
      have ha : raw7274step1 = raw7274step0 := by apply Matrix.ext; unfold raw7274step1 raw7274step0; decide +kernel
      have hl : raw7274step0Labels = labelEmbedding1 ∘ raw7274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7274step0 raw7274step0Labels raw7274step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3066 node3066Labels := by rfl

def raw7275 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw7275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7275 raw7275Labels = mixedMoment B node3497 node3497Labels := by
  calc
    mixedMoment B raw7275 raw7275Labels = mixedMoment B raw7275step0 raw7275step0Labels := by
      have ha : raw7275step0 = (fun i j => raw7275 (permutation185 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7275step0 raw7275; decide +kernel
      have hl : raw7275step0Labels = raw7275Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7275 raw7275Labels permutation185 permutation2
    mixedMoment B raw7275step0 raw7275step0Labels = mixedMoment B raw7275step1 raw7275step1Labels := by
      have ha : raw7275step1 = -raw7275step0 := by apply Matrix.ext; change ∀ i j, raw7275step1 i j = -(raw7275step0 i j); unfold raw7275step1 raw7275step0; decide +kernel
      have hl : raw7275step1Labels = raw7275step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3497 node3497Labels := by rfl

def raw7276 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7276 raw7276Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw7276 raw7276Labels = mixedMoment B raw7276step0 raw7276step0Labels := by
      have hz : ∀ j, raw7276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7276step0 = (fun i j => raw7276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7276step0 raw7276; decide +kernel
      have hl : raw7276step0Labels = raw7276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7276 raw7276Labels permutation434 hz
    mixedMoment B raw7276step0 raw7276step0Labels = mixedMoment B raw7276step1 raw7276step1Labels := by
      have ha : raw7276step1 = (fun i j => raw7276step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7276step1 raw7276step0; decide +kernel
      have hl : raw7276step1Labels = raw7276step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7276step0 raw7276step0Labels permutation38 permutation2
    mixedMoment B raw7276step1 raw7276step1Labels = mixedMoment B raw7276step2 raw7276step2Labels := by
      have ha : raw7276step2 = -raw7276step1 := by apply Matrix.ext; change ∀ i j, raw7276step2 i j = -(raw7276step1 i j); unfold raw7276step2 raw7276step1; decide +kernel
      have hl : raw7276step2Labels = raw7276step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw7277 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw7277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7277 raw7277Labels = mixedMoment B node3494 node3494Labels := by
  calc
    mixedMoment B raw7277 raw7277Labels = mixedMoment B raw7277step0 raw7277step0Labels := by
      have ha : raw7277step0 = (fun i j => raw7277 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7277step0 raw7277; decide +kernel
      have hl : raw7277step0Labels = raw7277Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7277 raw7277Labels permutation183 permutation2
    mixedMoment B raw7277step0 raw7277step0Labels = mixedMoment B raw7277step1 raw7277step1Labels := by
      have ha : raw7277step1 = -raw7277step0 := by apply Matrix.ext; change ∀ i j, raw7277step1 i j = -(raw7277step0 i j); unfold raw7277step1 raw7277step0; decide +kernel
      have hl : raw7277step1Labels = raw7277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3494 node3494Labels := by rfl

def raw7278 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7278 raw7278Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw7278 raw7278Labels = mixedMoment B raw7278step0 raw7278step0Labels := by
      have ha : raw7278step0 = (fun i j => raw7278 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7278step0 raw7278; decide +kernel
      have hl : raw7278step0Labels = raw7278Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7278 raw7278Labels permutation182 permutation2
    mixedMoment B raw7278step0 raw7278step0Labels = mixedMoment B raw7278step1 raw7278step1Labels := by
      have ha : raw7278step1 = -raw7278step0 := by apply Matrix.ext; change ∀ i j, raw7278step1 i j = -(raw7278step0 i j); unfold raw7278step1 raw7278step0; decide +kernel
      have hl : raw7278step1Labels = raw7278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3493 node3493Labels := by rfl

def raw7279 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw7279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7279 raw7279Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw7279 raw7279Labels = mixedMoment B raw7279step0 raw7279step0Labels := by
      have ha : raw7279step0 = (fun i j => raw7279 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7279step0 raw7279; decide +kernel
      have hl : raw7279step0Labels = raw7279Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7279 raw7279Labels permutation167 permutation4
    mixedMoment B raw7279step0 raw7279step0Labels = mixedMoment B raw7279step1 raw7279step1Labels := by
      have ha : raw7279step1 = -raw7279step0 := by apply Matrix.ext; change ∀ i j, raw7279step1 i j = -(raw7279step0 i j); unfold raw7279step1 raw7279step0; decide +kernel
      have hl : raw7279step1Labels = raw7279step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2021 node2021Labels := by rfl

def raw7280 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7280step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7280 raw7280Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw7280 raw7280Labels = mixedMoment B raw7280step0 raw7280step0Labels := by
      have ha : raw7280step0 = (fun i j => raw7280 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7280step0 raw7280; decide +kernel
      have hl : raw7280step0Labels = raw7280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7280 raw7280Labels permutation152 permutation4
    mixedMoment B raw7280step0 raw7280step0Labels = mixedMoment B raw7280step1 raw7280step1Labels := by
      have ha : raw7280step1 = -raw7280step0 := by apply Matrix.ext; change ∀ i j, raw7280step1 i j = -(raw7280step0 i j); unfold raw7280step1 raw7280step0; decide +kernel
      have hl : raw7280step1Labels = raw7280step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2051 node2051Labels := by rfl

def raw7281 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7281step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7281 raw7281Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw7281 raw7281Labels = mixedMoment B raw7281step0 raw7281step0Labels := by
      have ha : raw7281step0 = (fun i j => raw7281 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7281step0 raw7281; decide +kernel
      have hl : raw7281step0Labels = raw7281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7281 raw7281Labels permutation164 permutation4
    mixedMoment B raw7281step0 raw7281step0Labels = mixedMoment B raw7281step1 raw7281step1Labels := by
      have ha : raw7281step1 = -raw7281step0 := by apply Matrix.ext; change ∀ i j, raw7281step1 i j = -(raw7281step0 i j); unfold raw7281step1 raw7281step0; decide +kernel
      have hl : raw7281step1Labels = raw7281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2019 node2019Labels := by rfl

def raw7282 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7282Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7282step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw7282step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7282 raw7282Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw7282 raw7282Labels = mixedMoment B raw7282step0 raw7282step0Labels := by
      have hz : ∀ j, raw7282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7282step0 = (fun i j => raw7282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7282step0 raw7282; decide +kernel
      have hl : raw7282step0Labels = raw7282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7282 raw7282Labels permutation434 hz
    mixedMoment B raw7282step0 raw7282step0Labels = mixedMoment B raw7282step1 raw7282step1Labels := by
      have hz : ∀ j, raw7282step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7282step1 = (fun i j => raw7282step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7282step1 raw7282step0; decide +kernel
      have hl : raw7282step1Labels = raw7282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7282step0 raw7282step0Labels permutation56 hz
    mixedMoment B raw7282step1 raw7282step1Labels = mixedMoment B raw7282step2 raw7282step2Labels := by
      have ha : raw7282step2 = (fun i j => raw7282step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7282step2 raw7282step1; decide +kernel
      have hl : raw7282step2Labels = raw7282step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7282step1 raw7282step1Labels permutation10 permutation4
    mixedMoment B raw7282step2 raw7282step2Labels = mixedMoment B raw7282step3 raw7282step3Labels := by
      have ha : raw7282step3 = -raw7282step2 := by apply Matrix.ext; change ∀ i j, raw7282step3 i j = -(raw7282step2 i j); unfold raw7282step3 raw7282step2; decide +kernel
      have hl : raw7282step3Labels = raw7282step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3627 node3627Labels := by rfl

def raw7283 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7283Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7283step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7283 raw7283Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw7283 raw7283Labels = mixedMoment B raw7283step0 raw7283step0Labels := by
      have hz : ∀ j, raw7283 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7283step0 = (fun i j => raw7283 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7283step0 raw7283; decide +kernel
      have hl : raw7283step0Labels = raw7283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7283 raw7283Labels permutation265 hz
    mixedMoment B raw7283step0 raw7283step0Labels = mixedMoment B raw7283step1 raw7283step1Labels := by
      have ha : raw7283step1 = (fun i j => raw7283step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7283step1 raw7283step0; decide +kernel
      have hl : raw7283step1Labels = raw7283step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7283step0 raw7283step0Labels permutation44 permutation4
    mixedMoment B raw7283step1 raw7283step1Labels = mixedMoment B raw7283step2 raw7283step2Labels := by
      have ha : raw7283step2 = -raw7283step1 := by apply Matrix.ext; change ∀ i j, raw7283step2 i j = -(raw7283step1 i j); unfold raw7283step2 raw7283step1; decide +kernel
      have hl : raw7283step2Labels = raw7283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw7284 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7284Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw7284step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7284 raw7284Labels = mixedMoment B node3377 node3377Labels := by
  calc
    mixedMoment B raw7284 raw7284Labels = mixedMoment B raw7284step0 raw7284step0Labels := by
      have ha : raw7284step0 = (fun i j => raw7284 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7284step0 raw7284; decide +kernel
      have hl : raw7284step0Labels = raw7284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7284 raw7284Labels permutation167 permutation4
    mixedMoment B raw7284step0 raw7284step0Labels = mixedMoment B raw7284step1 raw7284step1Labels := by
      have ha : raw7284step1 = -raw7284step0 := by apply Matrix.ext; change ∀ i j, raw7284step1 i j = -(raw7284step0 i j); unfold raw7284step1 raw7284step0; decide +kernel
      have hl : raw7284step1Labels = raw7284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3377 node3377Labels := by rfl

def raw7285 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7285Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7285step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7285step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7285 raw7285Labels = mixedMoment B node3388 node3388Labels := by
  calc
    mixedMoment B raw7285 raw7285Labels = mixedMoment B raw7285step0 raw7285step0Labels := by
      have ha : raw7285step0 = (fun i j => raw7285 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7285step0 raw7285; decide +kernel
      have hl : raw7285step0Labels = raw7285Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7285 raw7285Labels permutation152 permutation4
    mixedMoment B raw7285step0 raw7285step0Labels = mixedMoment B raw7285step1 raw7285step1Labels := by
      have ha : raw7285step1 = -raw7285step0 := by apply Matrix.ext; change ∀ i j, raw7285step1 i j = -(raw7285step0 i j); unfold raw7285step1 raw7285step0; decide +kernel
      have hl : raw7285step1Labels = raw7285step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3388 node3388Labels := by rfl

def raw7286 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7286Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7286step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7286 raw7286Labels = mixedMoment B node3375 node3375Labels := by
  calc
    mixedMoment B raw7286 raw7286Labels = mixedMoment B raw7286step0 raw7286step0Labels := by
      have ha : raw7286step0 = (fun i j => raw7286 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7286step0 raw7286; decide +kernel
      have hl : raw7286step0Labels = raw7286Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7286 raw7286Labels permutation164 permutation4
    mixedMoment B raw7286step0 raw7286step0Labels = mixedMoment B raw7286step1 raw7286step1Labels := by
      have ha : raw7286step1 = -raw7286step0 := by apply Matrix.ext; change ∀ i j, raw7286step1 i j = -(raw7286step0 i j); unfold raw7286step1 raw7286step0; decide +kernel
      have hl : raw7286step1Labels = raw7286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3375 node3375Labels := by rfl

def raw7287 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7287Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7287 raw7287Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw7287 raw7287Labels = mixedMoment B raw7287step0 raw7287step0Labels := by
      have hz : ∀ j, raw7287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7287step0 = (fun i j => raw7287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7287step0 raw7287; decide +kernel
      have hl : raw7287step0Labels = raw7287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7287 raw7287Labels permutation434 hz
    mixedMoment B raw7287step0 raw7287step0Labels = mixedMoment B raw7287step1 raw7287step1Labels := by
      have ha : raw7287step1 = (fun i j => raw7287step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7287step1 raw7287step0; decide +kernel
      have hl : raw7287step1Labels = raw7287step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7287step0 raw7287step0Labels permutation32 permutation4
    mixedMoment B raw7287step1 raw7287step1Labels = mixedMoment B raw7287step2 raw7287step2Labels := by
      have ha : raw7287step2 = -raw7287step1 := by apply Matrix.ext; change ∀ i j, raw7287step2 i j = -(raw7287step1 i j); unfold raw7287step2 raw7287step1; decide +kernel
      have hl : raw7287step2Labels = raw7287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw7288 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7288Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw7288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7288 raw7288Labels = mixedMoment B node3504 node3504Labels := by
  calc
    mixedMoment B raw7288 raw7288Labels = mixedMoment B raw7288step0 raw7288step0Labels := by
      have ha : raw7288step0 = (fun i j => raw7288 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7288step0 raw7288; decide +kernel
      have hl : raw7288step0Labels = raw7288Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7288 raw7288Labels permutation167 permutation4
    mixedMoment B raw7288step0 raw7288step0Labels = mixedMoment B raw7288step1 raw7288step1Labels := by
      have ha : raw7288step1 = -raw7288step0 := by apply Matrix.ext; change ∀ i j, raw7288step1 i j = -(raw7288step0 i j); unfold raw7288step1 raw7288step0; decide +kernel
      have hl : raw7288step1Labels = raw7288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3504 node3504Labels := by rfl

def raw7289 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7289Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7289step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7289 raw7289Labels = mixedMoment B node3502 node3502Labels := by
  calc
    mixedMoment B raw7289 raw7289Labels = mixedMoment B raw7289step0 raw7289step0Labels := by
      have ha : raw7289step0 = (fun i j => raw7289 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7289step0 raw7289; decide +kernel
      have hl : raw7289step0Labels = raw7289Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7289 raw7289Labels permutation164 permutation4
    mixedMoment B raw7289step0 raw7289step0Labels = mixedMoment B raw7289step1 raw7289step1Labels := by
      have ha : raw7289step1 = -raw7289step0 := by apply Matrix.ext; change ∀ i j, raw7289step1 i j = -(raw7289step0 i j); unfold raw7289step1 raw7289step0; decide +kernel
      have hl : raw7289step1Labels = raw7289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3502 node3502Labels := by rfl

def raw7290 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7290Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7290step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7290 raw7290Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw7290 raw7290Labels = mixedMoment B raw7290step0 raw7290step0Labels := by
      have hz : ∀ j, raw7290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7290step0 = (fun i j => raw7290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7290step0 raw7290; decide +kernel
      have hl : raw7290step0Labels = raw7290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7290 raw7290Labels permutation434 hz
    mixedMoment B raw7290step0 raw7290step0Labels = mixedMoment B raw7290step1 raw7290step1Labels := by
      have ha : raw7290step1 = (fun i j => raw7290step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7290step1 raw7290step0; decide +kernel
      have hl : raw7290step1Labels = raw7290step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7290step0 raw7290step0Labels permutation34 permutation4
    mixedMoment B raw7290step1 raw7290step1Labels = mixedMoment B raw7290step2 raw7290step2Labels := by
      have ha : raw7290step2 = -raw7290step1 := by apply Matrix.ext; change ∀ i j, raw7290step2 i j = -(raw7290step1 i j); unfold raw7290step2 raw7290step1; decide +kernel
      have hl : raw7290step2Labels = raw7290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw7291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7291 raw7291Labels = mixedMoment B node5406 node5406Labels := by
  calc
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw7292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw7292step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7292step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7292step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7292step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7292 raw7292Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw7292 raw7292Labels = mixedMoment B raw7292step0 raw7292step0Labels := by
      have ha : raw7292step0 = (fun i j => raw7292 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7292step0 raw7292; decide +kernel
      have hl : raw7292step0Labels = raw7292Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7292 raw7292Labels permutation676 permutation3
    mixedMoment B raw7292step0 raw7292step0Labels = mixedMoment B raw7292step1 raw7292step1Labels := by
      have ha : raw7292step1 = -raw7292step0 := by apply Matrix.ext; change ∀ i j, raw7292step1 i j = -(raw7292step0 i j); unfold raw7292step1 raw7292step0; decide +kernel
      have hl : raw7292step1Labels = raw7292step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7292step1 raw7292step1Labels = mixedMoment B raw7292step2 raw7292step2Labels := by
      have ha : raw7292step2 = raw7292step1 := by apply Matrix.ext; unfold raw7292step2 raw7292step1; decide +kernel
      have hl : raw7292step1Labels = labelEmbedding6 ∘ raw7292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7292step1 raw7292step1Labels raw7292step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw7293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw7293step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7293step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7293step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7293 raw7293Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw7293 raw7293Labels = mixedMoment B raw7293step0 raw7293step0Labels := by
      have ha : raw7293step0 = (fun i j => raw7293 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7293step0 raw7293; decide +kernel
      have hl : raw7293step0Labels = raw7293Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7293 raw7293Labels permutation674 permutation3
    mixedMoment B raw7293step0 raw7293step0Labels = mixedMoment B raw7293step1 raw7293step1Labels := by
      have ha : raw7293step1 = -raw7293step0 := by apply Matrix.ext; change ∀ i j, raw7293step1 i j = -(raw7293step0 i j); unfold raw7293step1 raw7293step0; decide +kernel
      have hl : raw7293step1Labels = raw7293step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7293step1 raw7293step1Labels = mixedMoment B raw7293step2 raw7293step2Labels := by
      have ha : raw7293step2 = raw7293step1 := by apply Matrix.ext; unfold raw7293step2 raw7293step1; decide +kernel
      have hl : raw7293step1Labels = labelEmbedding6 ∘ raw7293step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7293step1 raw7293step1Labels raw7293step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw7294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw7294step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw7294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7294 raw7294Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw7294 raw7294Labels = mixedMoment B raw7294step0 raw7294step0Labels := by
      have ha : raw7294step0 = (fun i j => raw7294 (permutation602 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7294step0 raw7294; decide +kernel
      have hl : raw7294step0Labels = raw7294Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7294 raw7294Labels permutation602 permutation5
    mixedMoment B raw7294step0 raw7294step0Labels = mixedMoment B raw7294step1 raw7294step1Labels := by
      have ha : raw7294step1 = raw7294step0 := by apply Matrix.ext; unfold raw7294step1 raw7294step0; decide +kernel
      have hl : raw7294step0Labels = labelEmbedding8 ∘ raw7294step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7294step0 raw7294step0Labels raw7294step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw7295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7295step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7295step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7295step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7295 raw7295Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw7295 raw7295Labels = mixedMoment B raw7295step0 raw7295step0Labels := by
      have ha : raw7295step0 = (fun i j => raw7295 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7295step0 raw7295; decide +kernel
      have hl : raw7295step0Labels = raw7295Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7295 raw7295Labels permutation170 permutation7
    mixedMoment B raw7295step0 raw7295step0Labels = mixedMoment B raw7295step1 raw7295step1Labels := by
      have ha : raw7295step1 = -raw7295step0 := by apply Matrix.ext; change ∀ i j, raw7295step1 i j = -(raw7295step0 i j); unfold raw7295step1 raw7295step0; decide +kernel
      have hl : raw7295step1Labels = raw7295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7295step1 raw7295step1Labels = mixedMoment B raw7295step2 raw7295step2Labels := by
      have ha : raw7295step2 = raw7295step1 := by apply Matrix.ext; unfold raw7295step2 raw7295step1; decide +kernel
      have hl : raw7295step1Labels = labelEmbedding10 ∘ raw7295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7295step1 raw7295step1Labels raw7295step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
