import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33792step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33792step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33792step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33792step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33792 raw33792Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw33792 raw33792Labels = mixedMoment B raw33792step0 raw33792step0Labels := by
      have ha : raw33792step0 = (fun i j => raw33792 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33792step0 raw33792; decide +kernel
      have hl : raw33792step0Labels = raw33792Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33792 raw33792Labels permutation170 permutation7
    mixedMoment B raw33792step0 raw33792step0Labels = mixedMoment B raw33792step1 raw33792step1Labels := by
      have ha : raw33792step1 = -raw33792step0 := by apply Matrix.ext; change ∀ i j, raw33792step1 i j = -(raw33792step0 i j); unfold raw33792step1 raw33792step0; decide +kernel
      have hl : raw33792step1Labels = raw33792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33792step1 raw33792step1Labels = mixedMoment B raw33792step2 raw33792step2Labels := by
      have ha : raw33792step2 = raw33792step1 := by apply Matrix.ext; unfold raw33792step2 raw33792step1; decide +kernel
      have hl : raw33792step1Labels = labelEmbedding10 ∘ raw33792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33792step1 raw33792step1Labels raw33792step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

def raw33793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw33793step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33793step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33793step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33793 raw33793Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw33793 raw33793Labels = mixedMoment B raw33793step0 raw33793step0Labels := by
      have ha : raw33793step0 = (fun i j => raw33793 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33793step0 raw33793; decide +kernel
      have hl : raw33793step0Labels = raw33793Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33793 raw33793Labels permutation170 permutation7
    mixedMoment B raw33793step0 raw33793step0Labels = mixedMoment B raw33793step1 raw33793step1Labels := by
      have ha : raw33793step1 = -raw33793step0 := by apply Matrix.ext; change ∀ i j, raw33793step1 i j = -(raw33793step0 i j); unfold raw33793step1 raw33793step0; decide +kernel
      have hl : raw33793step1Labels = raw33793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33793step1 raw33793step1Labels = mixedMoment B raw33793step2 raw33793step2Labels := by
      have ha : raw33793step2 = raw33793step1 := by apply Matrix.ext; unfold raw33793step2 raw33793step1; decide +kernel
      have hl : raw33793step1Labels = labelEmbedding10 ∘ raw33793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33793step1 raw33793step1Labels raw33793step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw33794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw33794step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33794step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33794step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33794step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33794 raw33794Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw33794 raw33794Labels = mixedMoment B raw33794step0 raw33794step0Labels := by
      have ha : raw33794step0 = (fun i j => raw33794 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33794step0 raw33794; decide +kernel
      have hl : raw33794step0Labels = raw33794Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33794 raw33794Labels permutation171 permutation7
    mixedMoment B raw33794step0 raw33794step0Labels = mixedMoment B raw33794step1 raw33794step1Labels := by
      have ha : raw33794step1 = -raw33794step0 := by apply Matrix.ext; change ∀ i j, raw33794step1 i j = -(raw33794step0 i j); unfold raw33794step1 raw33794step0; decide +kernel
      have hl : raw33794step1Labels = raw33794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33794step1 raw33794step1Labels = mixedMoment B raw33794step2 raw33794step2Labels := by
      have ha : raw33794step2 = raw33794step1 := by apply Matrix.ext; unfold raw33794step2 raw33794step1; decide +kernel
      have hl : raw33794step1Labels = labelEmbedding10 ∘ raw33794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33794step1 raw33794step1Labels raw33794step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw33795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33795step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33795step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33795step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33795 raw33795Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw33795 raw33795Labels = mixedMoment B raw33795step0 raw33795step0Labels := by
      have ha : raw33795step0 = (fun i j => raw33795 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33795step0 raw33795; decide +kernel
      have hl : raw33795step0Labels = raw33795Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33795 raw33795Labels permutation170 permutation7
    mixedMoment B raw33795step0 raw33795step0Labels = mixedMoment B raw33795step1 raw33795step1Labels := by
      have ha : raw33795step1 = -raw33795step0 := by apply Matrix.ext; change ∀ i j, raw33795step1 i j = -(raw33795step0 i j); unfold raw33795step1 raw33795step0; decide +kernel
      have hl : raw33795step1Labels = raw33795step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33795step1 raw33795step1Labels = mixedMoment B raw33795step2 raw33795step2Labels := by
      have ha : raw33795step2 = raw33795step1 := by apply Matrix.ext; unfold raw33795step2 raw33795step1; decide +kernel
      have hl : raw33795step1Labels = labelEmbedding10 ∘ raw33795step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33795step1 raw33795step1Labels raw33795step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw33796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33796 raw33796Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw33796 raw33796Labels = mixedMoment B raw33796step0 raw33796step0Labels := by
      have hz : ∀ j, raw33796 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33796step0 = (fun i j => raw33796 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33796step0 raw33796; decide +kernel
      have hl : raw33796step0Labels = raw33796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33796 raw33796Labels permutation265 hz
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw33797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33797 raw33797Labels = mixedMoment B node4685 node4685Labels := by
  calc
    _ = mixedMoment B node4685 node4685Labels := by rfl

def raw33798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33798 raw33798Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw33798 raw33798Labels = mixedMoment B raw33798step0 raw33798step0Labels := by
      have ha : raw33798step0 = (fun i j => raw33798 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33798step0 raw33798; decide +kernel
      have hl : raw33798step0Labels = raw33798Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33798 raw33798Labels permutation158 permutation2
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw33799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33799 raw33799Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw33799 raw33799Labels = mixedMoment B raw33799step0 raw33799step0Labels := by
      have ha : raw33799step0 = (fun i j => raw33799 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33799step0 raw33799; decide +kernel
      have hl : raw33799step0Labels = raw33799Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33799 raw33799Labels permutation164 permutation2
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw33800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33800 raw33800Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw33800 raw33800Labels = mixedMoment B raw33800step0 raw33800step0Labels := by
      have ha : raw33800step0 = (fun i j => raw33800 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33800step0 raw33800; decide +kernel
      have hl : raw33800step0Labels = raw33800Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33800 raw33800Labels permutation155 permutation2
    _ = mixedMoment B node4332 node4332Labels := by rfl

def raw33801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33801step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33801 raw33801Labels = mixedMoment B node4668 node4668Labels := by
  calc
    mixedMoment B raw33801 raw33801Labels = mixedMoment B raw33801step0 raw33801step0Labels := by
      have ha : raw33801step0 = (fun i j => raw33801 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33801step0 raw33801; decide +kernel
      have hl : raw33801step0Labels = raw33801Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33801 raw33801Labels permutation155 permutation2
    _ = mixedMoment B node4668 node4668Labels := by rfl

def raw33802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33802 raw33802Labels = mixedMoment B node4775 node4775Labels := by
  calc
    mixedMoment B raw33802 raw33802Labels = mixedMoment B raw33802step0 raw33802step0Labels := by
      have ha : raw33802step0 = (fun i j => raw33802 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33802step0 raw33802; decide +kernel
      have hl : raw33802step0Labels = raw33802Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33802 raw33802Labels permutation155 permutation2
    _ = mixedMoment B node4775 node4775Labels := by rfl

def raw33803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33803 raw33803Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw33803 raw33803Labels = mixedMoment B raw33803step0 raw33803step0Labels := by
      have ha : raw33803step0 = (fun i j => raw33803 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33803step0 raw33803; decide +kernel
      have hl : raw33803step0Labels = raw33803Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33803 raw33803Labels permutation155 permutation2
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw33804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33804 raw33804Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw33804 raw33804Labels = mixedMoment B raw33804step0 raw33804step0Labels := by
      have ha : raw33804step0 = (fun i j => raw33804 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33804step0 raw33804; decide +kernel
      have hl : raw33804step0Labels = raw33804Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33804 raw33804Labels permutation157 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw33805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33805 raw33805Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw33805 raw33805Labels = mixedMoment B raw33805step0 raw33805step0Labels := by
      have ha : raw33805step0 = (fun i j => raw33805 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33805step0 raw33805; decide +kernel
      have hl : raw33805step0Labels = raw33805Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33805 raw33805Labels permutation153 permutation2
    _ = mixedMoment B node4332 node4332Labels := by rfl

def raw33806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33806 raw33806Labels = mixedMoment B node4668 node4668Labels := by
  calc
    mixedMoment B raw33806 raw33806Labels = mixedMoment B raw33806step0 raw33806step0Labels := by
      have ha : raw33806step0 = (fun i j => raw33806 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33806step0 raw33806; decide +kernel
      have hl : raw33806step0Labels = raw33806Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33806 raw33806Labels permutation153 permutation2
    _ = mixedMoment B node4668 node4668Labels := by rfl

def raw33807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33807 raw33807Labels = mixedMoment B node4775 node4775Labels := by
  calc
    mixedMoment B raw33807 raw33807Labels = mixedMoment B raw33807step0 raw33807step0Labels := by
      have ha : raw33807step0 = (fun i j => raw33807 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33807step0 raw33807; decide +kernel
      have hl : raw33807step0Labels = raw33807Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33807 raw33807Labels permutation153 permutation2
    _ = mixedMoment B node4775 node4775Labels := by rfl

def raw33808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33808 raw33808Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw33808 raw33808Labels = mixedMoment B raw33808step0 raw33808step0Labels := by
      have ha : raw33808step0 = (fun i j => raw33808 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33808step0 raw33808; decide +kernel
      have hl : raw33808step0Labels = raw33808Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33808 raw33808Labels permutation153 permutation2
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw33809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33809 raw33809Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw33809 raw33809Labels = mixedMoment B raw33809step0 raw33809step0Labels := by
      have ha : raw33809step0 = (fun i j => raw33809 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33809step0 raw33809; decide +kernel
      have hl : raw33809step0Labels = raw33809Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33809 raw33809Labels permutation156 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw33810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33810 raw33810Labels = mixedMoment B node4331 node4331Labels := by
  calc
    _ = mixedMoment B node4331 node4331Labels := by rfl

def raw33811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33811 raw33811Labels = mixedMoment B node4667 node4667Labels := by
  calc
    _ = mixedMoment B node4667 node4667Labels := by rfl

def raw33812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33812step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33812step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33812step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33812 raw33812Labels = mixedMoment B node4765 node4765Labels := by
  calc
    mixedMoment B raw33812 raw33812Labels = mixedMoment B raw33812step0 raw33812step0Labels := by
      have ha : raw33812step0 = (fun i j => raw33812 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33812step0 raw33812; decide +kernel
      have hl : raw33812step0Labels = raw33812Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33812 raw33812Labels permutation662 permutation3
    mixedMoment B raw33812step0 raw33812step0Labels = mixedMoment B raw33812step1 raw33812step1Labels := by
      have ha : raw33812step1 = -raw33812step0 := by apply Matrix.ext; change ∀ i j, raw33812step1 i j = -(raw33812step0 i j); unfold raw33812step1 raw33812step0; decide +kernel
      have hl : raw33812step1Labels = raw33812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33812step1 raw33812step1Labels = mixedMoment B raw33812step2 raw33812step2Labels := by
      have ha : raw33812step2 = raw33812step1 := by apply Matrix.ext; unfold raw33812step2 raw33812step1; decide +kernel
      have hl : raw33812step1Labels = labelEmbedding6 ∘ raw33812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33812step1 raw33812step1Labels raw33812step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4765 node4765Labels := by rfl

def raw33813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33813step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33813step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33813step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33813 raw33813Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw33813 raw33813Labels = mixedMoment B raw33813step0 raw33813step0Labels := by
      have ha : raw33813step0 = (fun i j => raw33813 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33813step0 raw33813; decide +kernel
      have hl : raw33813step0Labels = raw33813Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33813 raw33813Labels permutation170 permutation7
    mixedMoment B raw33813step0 raw33813step0Labels = mixedMoment B raw33813step1 raw33813step1Labels := by
      have ha : raw33813step1 = -raw33813step0 := by apply Matrix.ext; change ∀ i j, raw33813step1 i j = -(raw33813step0 i j); unfold raw33813step1 raw33813step0; decide +kernel
      have hl : raw33813step1Labels = raw33813step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33813step1 raw33813step1Labels = mixedMoment B raw33813step2 raw33813step2Labels := by
      have ha : raw33813step2 = raw33813step1 := by apply Matrix.ext; unfold raw33813step2 raw33813step1; decide +kernel
      have hl : raw33813step1Labels = labelEmbedding1 ∘ raw33813step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33813step1 raw33813step1Labels raw33813step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw33814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33814step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33814 raw33814Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw33814 raw33814Labels = mixedMoment B raw33814step0 raw33814step0Labels := by
      have ha : raw33814step0 = (fun i j => raw33814 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33814step0 raw33814; decide +kernel
      have hl : raw33814step0Labels = raw33814Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33814 raw33814Labels permutation170 permutation7
    mixedMoment B raw33814step0 raw33814step0Labels = mixedMoment B raw33814step1 raw33814step1Labels := by
      have ha : raw33814step1 = -raw33814step0 := by apply Matrix.ext; change ∀ i j, raw33814step1 i j = -(raw33814step0 i j); unfold raw33814step1 raw33814step0; decide +kernel
      have hl : raw33814step1Labels = raw33814step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33814step1 raw33814step1Labels = mixedMoment B raw33814step2 raw33814step2Labels := by
      have ha : raw33814step2 = raw33814step1 := by apply Matrix.ext; unfold raw33814step2 raw33814step1; decide +kernel
      have hl : raw33814step1Labels = labelEmbedding1 ∘ raw33814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33814step1 raw33814step1Labels raw33814step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw33815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw33815step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33815step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33815 raw33815Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw33815 raw33815Labels = mixedMoment B raw33815step0 raw33815step0Labels := by
      have ha : raw33815step0 = (fun i j => raw33815 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33815step0 raw33815; decide +kernel
      have hl : raw33815step0Labels = raw33815Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33815 raw33815Labels permutation170 permutation7
    mixedMoment B raw33815step0 raw33815step0Labels = mixedMoment B raw33815step1 raw33815step1Labels := by
      have ha : raw33815step1 = -raw33815step0 := by apply Matrix.ext; change ∀ i j, raw33815step1 i j = -(raw33815step0 i j); unfold raw33815step1 raw33815step0; decide +kernel
      have hl : raw33815step1Labels = raw33815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33815step1 raw33815step1Labels = mixedMoment B raw33815step2 raw33815step2Labels := by
      have ha : raw33815step2 = raw33815step1 := by apply Matrix.ext; unfold raw33815step2 raw33815step1; decide +kernel
      have hl : raw33815step1Labels = labelEmbedding1 ∘ raw33815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33815step1 raw33815step1Labels raw33815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw33816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw33816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33816step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33816 raw33816Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw33816 raw33816Labels = mixedMoment B raw33816step0 raw33816step0Labels := by
      have ha : raw33816step0 = (fun i j => raw33816 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33816step0 raw33816; decide +kernel
      have hl : raw33816step0Labels = raw33816Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33816 raw33816Labels permutation171 permutation7
    mixedMoment B raw33816step0 raw33816step0Labels = mixedMoment B raw33816step1 raw33816step1Labels := by
      have ha : raw33816step1 = -raw33816step0 := by apply Matrix.ext; change ∀ i j, raw33816step1 i j = -(raw33816step0 i j); unfold raw33816step1 raw33816step0; decide +kernel
      have hl : raw33816step1Labels = raw33816step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33816step1 raw33816step1Labels = mixedMoment B raw33816step2 raw33816step2Labels := by
      have ha : raw33816step2 = raw33816step1 := by apply Matrix.ext; unfold raw33816step2 raw33816step1; decide +kernel
      have hl : raw33816step1Labels = labelEmbedding1 ∘ raw33816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33816step1 raw33816step1Labels raw33816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw33817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33817step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33817step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33817step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33817 raw33817Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw33817 raw33817Labels = mixedMoment B raw33817step0 raw33817step0Labels := by
      have ha : raw33817step0 = (fun i j => raw33817 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33817step0 raw33817; decide +kernel
      have hl : raw33817step0Labels = raw33817Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33817 raw33817Labels permutation170 permutation7
    mixedMoment B raw33817step0 raw33817step0Labels = mixedMoment B raw33817step1 raw33817step1Labels := by
      have ha : raw33817step1 = -raw33817step0 := by apply Matrix.ext; change ∀ i j, raw33817step1 i j = -(raw33817step0 i j); unfold raw33817step1 raw33817step0; decide +kernel
      have hl : raw33817step1Labels = raw33817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33817step1 raw33817step1Labels = mixedMoment B raw33817step2 raw33817step2Labels := by
      have ha : raw33817step2 = raw33817step1 := by apply Matrix.ext; unfold raw33817step2 raw33817step1; decide +kernel
      have hl : raw33817step1Labels = labelEmbedding1 ∘ raw33817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33817step1 raw33817step1Labels raw33817step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw33818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33818step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33818step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33818step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33818 raw33818Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw33818 raw33818Labels = mixedMoment B raw33818step0 raw33818step0Labels := by
      have hz : ∀ j, raw33818 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33818step0 = (fun i j => raw33818 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33818step0 raw33818; decide +kernel
      have hl : raw33818step0Labels = raw33818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33818 raw33818Labels permutation265 hz
    mixedMoment B raw33818step0 raw33818step0Labels = mixedMoment B raw33818step1 raw33818step1Labels := by
      have ha : raw33818step1 = (fun i j => raw33818step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33818step1 raw33818step0; decide +kernel
      have hl : raw33818step1Labels = raw33818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33818step0 raw33818step0Labels permutation50 permutation7
    mixedMoment B raw33818step1 raw33818step1Labels = mixedMoment B raw33818step2 raw33818step2Labels := by
      have ha : raw33818step2 = -raw33818step1 := by apply Matrix.ext; change ∀ i j, raw33818step2 i j = -(raw33818step1 i j); unfold raw33818step2 raw33818step1; decide +kernel
      have hl : raw33818step2Labels = raw33818step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33818step2 raw33818step2Labels = mixedMoment B raw33818step3 raw33818step3Labels := by
      have ha : raw33818step3 = raw33818step2 := by apply Matrix.ext; unfold raw33818step3 raw33818step2; decide +kernel
      have hl : raw33818step2Labels = labelEmbedding1 ∘ raw33818step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33818step2 raw33818step2Labels raw33818step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw33819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33819step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33819step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33819step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33819step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33819step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33819 raw33819Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw33819 raw33819Labels = mixedMoment B raw33819step0 raw33819step0Labels := by
      have hz : ∀ j, raw33819 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33819step0 = (fun i j => raw33819 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33819step0 raw33819; decide +kernel
      have hl : raw33819step0Labels = raw33819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33819 raw33819Labels permutation265 hz
    mixedMoment B raw33819step0 raw33819step0Labels = mixedMoment B raw33819step1 raw33819step1Labels := by
      have ha : raw33819step1 = (fun i j => raw33819step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33819step1 raw33819step0; decide +kernel
      have hl : raw33819step1Labels = raw33819step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33819step0 raw33819step0Labels permutation50 permutation7
    mixedMoment B raw33819step1 raw33819step1Labels = mixedMoment B raw33819step2 raw33819step2Labels := by
      have ha : raw33819step2 = -raw33819step1 := by apply Matrix.ext; change ∀ i j, raw33819step2 i j = -(raw33819step1 i j); unfold raw33819step2 raw33819step1; decide +kernel
      have hl : raw33819step2Labels = raw33819step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33819step2 raw33819step2Labels = mixedMoment B raw33819step3 raw33819step3Labels := by
      have ha : raw33819step3 = raw33819step2 := by apply Matrix.ext; unfold raw33819step3 raw33819step2; decide +kernel
      have hl : raw33819step2Labels = labelEmbedding1 ∘ raw33819step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33819step2 raw33819step2Labels raw33819step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw33820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33820step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33820step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33820step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33820step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33820 raw33820Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw33820 raw33820Labels = mixedMoment B raw33820step0 raw33820step0Labels := by
      have hz : ∀ j, raw33820 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33820step0 = (fun i j => raw33820 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33820step0 raw33820; decide +kernel
      have hl : raw33820step0Labels = raw33820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33820 raw33820Labels permutation265 hz
    mixedMoment B raw33820step0 raw33820step0Labels = mixedMoment B raw33820step1 raw33820step1Labels := by
      have ha : raw33820step1 = (fun i j => raw33820step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33820step1 raw33820step0; decide +kernel
      have hl : raw33820step1Labels = raw33820step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33820step0 raw33820step0Labels permutation50 permutation7
    mixedMoment B raw33820step1 raw33820step1Labels = mixedMoment B raw33820step2 raw33820step2Labels := by
      have ha : raw33820step2 = -raw33820step1 := by apply Matrix.ext; change ∀ i j, raw33820step2 i j = -(raw33820step1 i j); unfold raw33820step2 raw33820step1; decide +kernel
      have hl : raw33820step2Labels = raw33820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33820step2 raw33820step2Labels = mixedMoment B raw33820step3 raw33820step3Labels := by
      have ha : raw33820step3 = raw33820step2 := by apply Matrix.ext; unfold raw33820step3 raw33820step2; decide +kernel
      have hl : raw33820step2Labels = labelEmbedding1 ∘ raw33820step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33820step2 raw33820step2Labels raw33820step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw33821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33821step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33821step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33821step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33821step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33821 raw33821Labels = mixedMoment B node1680 node1680Labels := by
  calc
    mixedMoment B raw33821 raw33821Labels = mixedMoment B raw33821step0 raw33821step0Labels := by
      have ha : raw33821step0 = (fun i j => raw33821 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33821step0 raw33821; decide +kernel
      have hl : raw33821step0Labels = raw33821Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33821 raw33821Labels permutation170 permutation7
    mixedMoment B raw33821step0 raw33821step0Labels = mixedMoment B raw33821step1 raw33821step1Labels := by
      have ha : raw33821step1 = -raw33821step0 := by apply Matrix.ext; change ∀ i j, raw33821step1 i j = -(raw33821step0 i j); unfold raw33821step1 raw33821step0; decide +kernel
      have hl : raw33821step1Labels = raw33821step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33821step1 raw33821step1Labels = mixedMoment B raw33821step2 raw33821step2Labels := by
      have ha : raw33821step2 = raw33821step1 := by apply Matrix.ext; unfold raw33821step2 raw33821step1; decide +kernel
      have hl : raw33821step1Labels = labelEmbedding1 ∘ raw33821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33821step1 raw33821step1Labels raw33821step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1680 node1680Labels := by rfl

def raw33822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33822step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33822step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33822step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33822 raw33822Labels = mixedMoment B node2156 node2156Labels := by
  calc
    mixedMoment B raw33822 raw33822Labels = mixedMoment B raw33822step0 raw33822step0Labels := by
      have ha : raw33822step0 = (fun i j => raw33822 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33822step0 raw33822; decide +kernel
      have hl : raw33822step0Labels = raw33822Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33822 raw33822Labels permutation170 permutation7
    mixedMoment B raw33822step0 raw33822step0Labels = mixedMoment B raw33822step1 raw33822step1Labels := by
      have ha : raw33822step1 = -raw33822step0 := by apply Matrix.ext; change ∀ i j, raw33822step1 i j = -(raw33822step0 i j); unfold raw33822step1 raw33822step0; decide +kernel
      have hl : raw33822step1Labels = raw33822step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33822step1 raw33822step1Labels = mixedMoment B raw33822step2 raw33822step2Labels := by
      have ha : raw33822step2 = raw33822step1 := by apply Matrix.ext; unfold raw33822step2 raw33822step1; decide +kernel
      have hl : raw33822step1Labels = labelEmbedding1 ∘ raw33822step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33822step1 raw33822step1Labels raw33822step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2156 node2156Labels := by rfl

def raw33823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33823step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33823step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33823step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33823step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33823 raw33823Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw33823 raw33823Labels = mixedMoment B raw33823step0 raw33823step0Labels := by
      have ha : raw33823step0 = (fun i j => raw33823 (permutation172 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33823step0 raw33823; decide +kernel
      have hl : raw33823step0Labels = raw33823Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33823 raw33823Labels permutation172 permutation7
    mixedMoment B raw33823step0 raw33823step0Labels = mixedMoment B raw33823step1 raw33823step1Labels := by
      have ha : raw33823step1 = -raw33823step0 := by apply Matrix.ext; change ∀ i j, raw33823step1 i j = -(raw33823step0 i j); unfold raw33823step1 raw33823step0; decide +kernel
      have hl : raw33823step1Labels = raw33823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33823step1 raw33823step1Labels = mixedMoment B raw33823step2 raw33823step2Labels := by
      have ha : raw33823step2 = raw33823step1 := by apply Matrix.ext; unfold raw33823step2 raw33823step1; decide +kernel
      have hl : raw33823step1Labels = labelEmbedding1 ∘ raw33823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33823step1 raw33823step1Labels raw33823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw33824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33824step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33824step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33824 raw33824Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw33824 raw33824Labels = mixedMoment B raw33824step0 raw33824step0Labels := by
      have ha : raw33824step0 = (fun i j => raw33824 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33824step0 raw33824; decide +kernel
      have hl : raw33824step0Labels = raw33824Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33824 raw33824Labels permutation174 permutation7
    mixedMoment B raw33824step0 raw33824step0Labels = mixedMoment B raw33824step1 raw33824step1Labels := by
      have ha : raw33824step1 = -raw33824step0 := by apply Matrix.ext; change ∀ i j, raw33824step1 i j = -(raw33824step0 i j); unfold raw33824step1 raw33824step0; decide +kernel
      have hl : raw33824step1Labels = raw33824step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33824step1 raw33824step1Labels = mixedMoment B raw33824step2 raw33824step2Labels := by
      have ha : raw33824step2 = raw33824step1 := by apply Matrix.ext; unfold raw33824step2 raw33824step1; decide +kernel
      have hl : raw33824step1Labels = labelEmbedding1 ∘ raw33824step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33824step1 raw33824step1Labels raw33824step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw33825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33825step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33825step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33825step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33825 raw33825Labels = mixedMoment B node2204 node2204Labels := by
  calc
    mixedMoment B raw33825 raw33825Labels = mixedMoment B raw33825step0 raw33825step0Labels := by
      have ha : raw33825step0 = (fun i j => raw33825 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33825step0 raw33825; decide +kernel
      have hl : raw33825step0Labels = raw33825Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33825 raw33825Labels permutation170 permutation7
    mixedMoment B raw33825step0 raw33825step0Labels = mixedMoment B raw33825step1 raw33825step1Labels := by
      have ha : raw33825step1 = -raw33825step0 := by apply Matrix.ext; change ∀ i j, raw33825step1 i j = -(raw33825step0 i j); unfold raw33825step1 raw33825step0; decide +kernel
      have hl : raw33825step1Labels = raw33825step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33825step1 raw33825step1Labels = mixedMoment B raw33825step2 raw33825step2Labels := by
      have ha : raw33825step2 = raw33825step1 := by apply Matrix.ext; unfold raw33825step2 raw33825step1; decide +kernel
      have hl : raw33825step1Labels = labelEmbedding1 ∘ raw33825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33825step1 raw33825step1Labels raw33825step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2204 node2204Labels := by rfl

def raw33826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33826Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33826step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33826step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33826step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33826 raw33826Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw33826 raw33826Labels = mixedMoment B raw33826step0 raw33826step0Labels := by
      have ha : raw33826step0 = (fun i j => raw33826 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33826step0 raw33826; decide +kernel
      have hl : raw33826step0Labels = raw33826Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33826 raw33826Labels permutation171 permutation7
    mixedMoment B raw33826step0 raw33826step0Labels = mixedMoment B raw33826step1 raw33826step1Labels := by
      have ha : raw33826step1 = -raw33826step0 := by apply Matrix.ext; change ∀ i j, raw33826step1 i j = -(raw33826step0 i j); unfold raw33826step1 raw33826step0; decide +kernel
      have hl : raw33826step1Labels = raw33826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33826step1 raw33826step1Labels = mixedMoment B raw33826step2 raw33826step2Labels := by
      have ha : raw33826step2 = raw33826step1 := by apply Matrix.ext; unfold raw33826step2 raw33826step1; decide +kernel
      have hl : raw33826step1Labels = labelEmbedding1 ∘ raw33826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33826step1 raw33826step1Labels raw33826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

def raw33827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33827Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33827step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33827step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33827step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33827 raw33827Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw33827 raw33827Labels = mixedMoment B raw33827step0 raw33827step0Labels := by
      have ha : raw33827step0 = (fun i j => raw33827 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33827step0 raw33827; decide +kernel
      have hl : raw33827step0Labels = raw33827Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33827 raw33827Labels permutation171 permutation7
    mixedMoment B raw33827step0 raw33827step0Labels = mixedMoment B raw33827step1 raw33827step1Labels := by
      have ha : raw33827step1 = -raw33827step0 := by apply Matrix.ext; change ∀ i j, raw33827step1 i j = -(raw33827step0 i j); unfold raw33827step1 raw33827step0; decide +kernel
      have hl : raw33827step1Labels = raw33827step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33827step1 raw33827step1Labels = mixedMoment B raw33827step2 raw33827step2Labels := by
      have ha : raw33827step2 = raw33827step1 := by apply Matrix.ext; unfold raw33827step2 raw33827step1; decide +kernel
      have hl : raw33827step1Labels = labelEmbedding1 ∘ raw33827step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33827step1 raw33827step1Labels raw33827step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

def raw33828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33828step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33828step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33828step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33828 raw33828Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw33828 raw33828Labels = mixedMoment B raw33828step0 raw33828step0Labels := by
      have ha : raw33828step0 = (fun i j => raw33828 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33828step0 raw33828; decide +kernel
      have hl : raw33828step0Labels = raw33828Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33828 raw33828Labels permutation171 permutation7
    mixedMoment B raw33828step0 raw33828step0Labels = mixedMoment B raw33828step1 raw33828step1Labels := by
      have ha : raw33828step1 = -raw33828step0 := by apply Matrix.ext; change ∀ i j, raw33828step1 i j = -(raw33828step0 i j); unfold raw33828step1 raw33828step0; decide +kernel
      have hl : raw33828step1Labels = raw33828step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33828step1 raw33828step1Labels = mixedMoment B raw33828step2 raw33828step2Labels := by
      have ha : raw33828step2 = raw33828step1 := by apply Matrix.ext; unfold raw33828step2 raw33828step1; decide +kernel
      have hl : raw33828step1Labels = labelEmbedding1 ∘ raw33828step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33828step1 raw33828step1Labels raw33828step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

def raw33829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33829Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33829step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33829step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33829step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33829 raw33829Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw33829 raw33829Labels = mixedMoment B raw33829step0 raw33829step0Labels := by
      have ha : raw33829step0 = (fun i j => raw33829 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33829step0 raw33829; decide +kernel
      have hl : raw33829step0Labels = raw33829Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33829 raw33829Labels permutation171 permutation7
    mixedMoment B raw33829step0 raw33829step0Labels = mixedMoment B raw33829step1 raw33829step1Labels := by
      have ha : raw33829step1 = -raw33829step0 := by apply Matrix.ext; change ∀ i j, raw33829step1 i j = -(raw33829step0 i j); unfold raw33829step1 raw33829step0; decide +kernel
      have hl : raw33829step1Labels = raw33829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33829step1 raw33829step1Labels = mixedMoment B raw33829step2 raw33829step2Labels := by
      have ha : raw33829step2 = raw33829step1 := by apply Matrix.ext; unfold raw33829step2 raw33829step1; decide +kernel
      have hl : raw33829step1Labels = labelEmbedding1 ∘ raw33829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33829step1 raw33829step1Labels raw33829step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw33830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33830Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33830step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33830step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33830 raw33830Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw33830 raw33830Labels = mixedMoment B raw33830step0 raw33830step0Labels := by
      have ha : raw33830step0 = (fun i j => raw33830 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33830step0 raw33830; decide +kernel
      have hl : raw33830step0Labels = raw33830Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33830 raw33830Labels permutation171 permutation7
    mixedMoment B raw33830step0 raw33830step0Labels = mixedMoment B raw33830step1 raw33830step1Labels := by
      have ha : raw33830step1 = -raw33830step0 := by apply Matrix.ext; change ∀ i j, raw33830step1 i j = -(raw33830step0 i j); unfold raw33830step1 raw33830step0; decide +kernel
      have hl : raw33830step1Labels = raw33830step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33830step1 raw33830step1Labels = mixedMoment B raw33830step2 raw33830step2Labels := by
      have ha : raw33830step2 = raw33830step1 := by apply Matrix.ext; unfold raw33830step2 raw33830step1; decide +kernel
      have hl : raw33830step1Labels = labelEmbedding1 ∘ raw33830step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33830step1 raw33830step1Labels raw33830step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw33831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33831Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33831step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33831step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33831step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33831step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33831 raw33831Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw33831 raw33831Labels = mixedMoment B raw33831step0 raw33831step0Labels := by
      have ha : raw33831step0 = (fun i j => raw33831 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33831step0 raw33831; decide +kernel
      have hl : raw33831step0Labels = raw33831Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33831 raw33831Labels permutation170 permutation7
    mixedMoment B raw33831step0 raw33831step0Labels = mixedMoment B raw33831step1 raw33831step1Labels := by
      have ha : raw33831step1 = -raw33831step0 := by apply Matrix.ext; change ∀ i j, raw33831step1 i j = -(raw33831step0 i j); unfold raw33831step1 raw33831step0; decide +kernel
      have hl : raw33831step1Labels = raw33831step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33831step1 raw33831step1Labels = mixedMoment B raw33831step2 raw33831step2Labels := by
      have ha : raw33831step2 = raw33831step1 := by apply Matrix.ext; unfold raw33831step2 raw33831step1; decide +kernel
      have hl : raw33831step1Labels = labelEmbedding1 ∘ raw33831step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33831step1 raw33831step1Labels raw33831step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

def raw33832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33832Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33832step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33832 raw33832Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw33832 raw33832Labels = mixedMoment B raw33832step0 raw33832step0Labels := by
      have ha : raw33832step0 = (fun i j => raw33832 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33832step0 raw33832; decide +kernel
      have hl : raw33832step0Labels = raw33832Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33832 raw33832Labels permutation170 permutation7
    mixedMoment B raw33832step0 raw33832step0Labels = mixedMoment B raw33832step1 raw33832step1Labels := by
      have ha : raw33832step1 = -raw33832step0 := by apply Matrix.ext; change ∀ i j, raw33832step1 i j = -(raw33832step0 i j); unfold raw33832step1 raw33832step0; decide +kernel
      have hl : raw33832step1Labels = raw33832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33832step1 raw33832step1Labels = mixedMoment B raw33832step2 raw33832step2Labels := by
      have ha : raw33832step2 = raw33832step1 := by apply Matrix.ext; unfold raw33832step2 raw33832step1; decide +kernel
      have hl : raw33832step1Labels = labelEmbedding1 ∘ raw33832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33832step1 raw33832step1Labels raw33832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

def raw33833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33833Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33833step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33833step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33833 raw33833Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw33833 raw33833Labels = mixedMoment B raw33833step0 raw33833step0Labels := by
      have ha : raw33833step0 = (fun i j => raw33833 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33833step0 raw33833; decide +kernel
      have hl : raw33833step0Labels = raw33833Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33833 raw33833Labels permutation170 permutation7
    mixedMoment B raw33833step0 raw33833step0Labels = mixedMoment B raw33833step1 raw33833step1Labels := by
      have ha : raw33833step1 = -raw33833step0 := by apply Matrix.ext; change ∀ i j, raw33833step1 i j = -(raw33833step0 i j); unfold raw33833step1 raw33833step0; decide +kernel
      have hl : raw33833step1Labels = raw33833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33833step1 raw33833step1Labels = mixedMoment B raw33833step2 raw33833step2Labels := by
      have ha : raw33833step2 = raw33833step1 := by apply Matrix.ext; unfold raw33833step2 raw33833step1; decide +kernel
      have hl : raw33833step1Labels = labelEmbedding1 ∘ raw33833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33833step1 raw33833step1Labels raw33833step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

def raw33834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33834Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33834step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33834step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33834step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33834 raw33834Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw33834 raw33834Labels = mixedMoment B raw33834step0 raw33834step0Labels := by
      have ha : raw33834step0 = (fun i j => raw33834 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33834step0 raw33834; decide +kernel
      have hl : raw33834step0Labels = raw33834Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33834 raw33834Labels permutation170 permutation7
    mixedMoment B raw33834step0 raw33834step0Labels = mixedMoment B raw33834step1 raw33834step1Labels := by
      have ha : raw33834step1 = -raw33834step0 := by apply Matrix.ext; change ∀ i j, raw33834step1 i j = -(raw33834step0 i j); unfold raw33834step1 raw33834step0; decide +kernel
      have hl : raw33834step1Labels = raw33834step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33834step1 raw33834step1Labels = mixedMoment B raw33834step2 raw33834step2Labels := by
      have ha : raw33834step2 = raw33834step1 := by apply Matrix.ext; unfold raw33834step2 raw33834step1; decide +kernel
      have hl : raw33834step1Labels = labelEmbedding1 ∘ raw33834step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33834step1 raw33834step1Labels raw33834step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw33835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33835Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33835step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33835step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33835step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33835 raw33835Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw33835 raw33835Labels = mixedMoment B raw33835step0 raw33835step0Labels := by
      have ha : raw33835step0 = (fun i j => raw33835 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33835step0 raw33835; decide +kernel
      have hl : raw33835step0Labels = raw33835Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33835 raw33835Labels permutation170 permutation7
    mixedMoment B raw33835step0 raw33835step0Labels = mixedMoment B raw33835step1 raw33835step1Labels := by
      have ha : raw33835step1 = -raw33835step0 := by apply Matrix.ext; change ∀ i j, raw33835step1 i j = -(raw33835step0 i j); unfold raw33835step1 raw33835step0; decide +kernel
      have hl : raw33835step1Labels = raw33835step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33835step1 raw33835step1Labels = mixedMoment B raw33835step2 raw33835step2Labels := by
      have ha : raw33835step2 = raw33835step1 := by apply Matrix.ext; unfold raw33835step2 raw33835step1; decide +kernel
      have hl : raw33835step1Labels = labelEmbedding1 ∘ raw33835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33835step1 raw33835step1Labels raw33835step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw33836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33836step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33836step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33836 raw33836Labels = mixedMoment B node1684 node1684Labels := by
  calc
    mixedMoment B raw33836 raw33836Labels = mixedMoment B raw33836step0 raw33836step0Labels := by
      have ha : raw33836step0 = (fun i j => raw33836 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33836step0 raw33836; decide +kernel
      have hl : raw33836step0Labels = raw33836Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33836 raw33836Labels permutation170 permutation7
    mixedMoment B raw33836step0 raw33836step0Labels = mixedMoment B raw33836step1 raw33836step1Labels := by
      have ha : raw33836step1 = -raw33836step0 := by apply Matrix.ext; change ∀ i j, raw33836step1 i j = -(raw33836step0 i j); unfold raw33836step1 raw33836step0; decide +kernel
      have hl : raw33836step1Labels = raw33836step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33836step1 raw33836step1Labels = mixedMoment B raw33836step2 raw33836step2Labels := by
      have ha : raw33836step2 = raw33836step1 := by apply Matrix.ext; unfold raw33836step2 raw33836step1; decide +kernel
      have hl : raw33836step1Labels = labelEmbedding1 ∘ raw33836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33836step1 raw33836step1Labels raw33836step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1684 node1684Labels := by rfl

def raw33837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33837step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33837step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33837step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33837 raw33837Labels = mixedMoment B node2160 node2160Labels := by
  calc
    mixedMoment B raw33837 raw33837Labels = mixedMoment B raw33837step0 raw33837step0Labels := by
      have ha : raw33837step0 = (fun i j => raw33837 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33837step0 raw33837; decide +kernel
      have hl : raw33837step0Labels = raw33837Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33837 raw33837Labels permutation170 permutation7
    mixedMoment B raw33837step0 raw33837step0Labels = mixedMoment B raw33837step1 raw33837step1Labels := by
      have ha : raw33837step1 = -raw33837step0 := by apply Matrix.ext; change ∀ i j, raw33837step1 i j = -(raw33837step0 i j); unfold raw33837step1 raw33837step0; decide +kernel
      have hl : raw33837step1Labels = raw33837step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33837step1 raw33837step1Labels = mixedMoment B raw33837step2 raw33837step2Labels := by
      have ha : raw33837step2 = raw33837step1 := by apply Matrix.ext; unfold raw33837step2 raw33837step1; decide +kernel
      have hl : raw33837step1Labels = labelEmbedding1 ∘ raw33837step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33837step1 raw33837step1Labels raw33837step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2160 node2160Labels := by rfl

def raw33838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw33838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw33838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33838 raw33838Labels = mixedMoment B node2179 node2179Labels := by
  calc
    mixedMoment B raw33838 raw33838Labels = mixedMoment B raw33838step0 raw33838step0Labels := by
      have ha : raw33838step0 = (fun i j => raw33838 (permutation659 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33838step0 raw33838; decide +kernel
      have hl : raw33838step0Labels = raw33838Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33838 raw33838Labels permutation659 permutation5
    mixedMoment B raw33838step0 raw33838step0Labels = mixedMoment B raw33838step1 raw33838step1Labels := by
      have ha : raw33838step1 = raw33838step0 := by apply Matrix.ext; unfold raw33838step1 raw33838step0; decide +kernel
      have hl : raw33838step0Labels = labelEmbedding1 ∘ raw33838step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33838step0 raw33838step0Labels raw33838step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2179 node2179Labels := by rfl

def raw33839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33839 raw33839Labels = mixedMoment B node3378 node3378Labels := by
  calc
    _ = mixedMoment B node3378 node3378Labels := by rfl

def raw33840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33840 raw33840Labels = mixedMoment B node2023 node2023Labels := by
  calc
    _ = mixedMoment B node2023 node2023Labels := by rfl

def raw33841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33841 raw33841Labels = mixedMoment B node1811 node1811Labels := by
  calc
    _ = mixedMoment B node1811 node1811Labels := by rfl

def raw33842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33842 raw33842Labels = mixedMoment B node1794 node1794Labels := by
  calc
    mixedMoment B raw33842 raw33842Labels = mixedMoment B raw33842step0 raw33842step0Labels := by
      have ha : raw33842step0 = (fun i j => raw33842 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33842step0 raw33842; decide +kernel
      have hl : raw33842step0Labels = raw33842Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33842 raw33842Labels permutation155 permutation2
    _ = mixedMoment B node1794 node1794Labels := by rfl

def raw33843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33843 raw33843Labels = mixedMoment B node1794 node1794Labels := by
  calc
    mixedMoment B raw33843 raw33843Labels = mixedMoment B raw33843step0 raw33843step0Labels := by
      have ha : raw33843step0 = (fun i j => raw33843 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33843step0 raw33843; decide +kernel
      have hl : raw33843step0Labels = raw33843Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33843 raw33843Labels permutation153 permutation2
    _ = mixedMoment B node1794 node1794Labels := by rfl

def raw33844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33844 raw33844Labels = mixedMoment B node1793 node1793Labels := by
  calc
    _ = mixedMoment B node1793 node1793Labels := by rfl

def raw33845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33845step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33845 raw33845Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw33845 raw33845Labels = mixedMoment B raw33845step0 raw33845step0Labels := by
      have ha : raw33845step0 = (fun i j => raw33845 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33845step0 raw33845; decide +kernel
      have hl : raw33845step0Labels = raw33845Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33845 raw33845Labels permutation152 permutation3
    mixedMoment B raw33845step0 raw33845step0Labels = mixedMoment B raw33845step1 raw33845step1Labels := by
      have ha : raw33845step1 = raw33845step0 := by apply Matrix.ext; unfold raw33845step1 raw33845step0; decide +kernel
      have hl : raw33845step0Labels = labelEmbedding6 ∘ raw33845step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33845step0 raw33845step0Labels raw33845step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw33846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw33846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33846 raw33846Labels = mixedMoment B node5417 node5417Labels := by
  calc
    mixedMoment B raw33846 raw33846Labels = mixedMoment B raw33846step0 raw33846step0Labels := by
      have ha : raw33846step0 = (fun i j => raw33846 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33846step0 raw33846; decide +kernel
      have hl : raw33846step0Labels = raw33846Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33846 raw33846Labels permutation662 permutation2
    mixedMoment B raw33846step0 raw33846step0Labels = mixedMoment B raw33846step1 raw33846step1Labels := by
      have ha : raw33846step1 = -raw33846step0 := by apply Matrix.ext; change ∀ i j, raw33846step1 i j = -(raw33846step0 i j); unfold raw33846step1 raw33846step0; decide +kernel
      have hl : raw33846step1Labels = raw33846step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5417 node5417Labels := by rfl

def raw33847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw33847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33847step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33847step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33847 raw33847Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw33847 raw33847Labels = mixedMoment B raw33847step0 raw33847step0Labels := by
      have hz : ∀ j, raw33847 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33847step0 = (fun i j => raw33847 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33847step0 raw33847; decide +kernel
      have hl : raw33847step0Labels = raw33847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33847 raw33847Labels permutation520 hz
    mixedMoment B raw33847step0 raw33847step0Labels = mixedMoment B raw33847step1 raw33847step1Labels := by
      have ha : raw33847step1 = (fun i j => raw33847step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33847step1 raw33847step0; decide +kernel
      have hl : raw33847step1Labels = raw33847step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33847step0 raw33847step0Labels permutation151 permutation2
    mixedMoment B raw33847step1 raw33847step1Labels = mixedMoment B raw33847step2 raw33847step2Labels := by
      have ha : raw33847step2 = -raw33847step1 := by apply Matrix.ext; change ∀ i j, raw33847step2 i j = -(raw33847step1 i j); unfold raw33847step2 raw33847step1; decide +kernel
      have hl : raw33847step2Labels = raw33847step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw33848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33848step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33848 raw33848Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw33848 raw33848Labels = mixedMoment B raw33848step0 raw33848step0Labels := by
      have ha : raw33848step0 = (fun i j => raw33848 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33848step0 raw33848; decide +kernel
      have hl : raw33848step0Labels = raw33848Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33848 raw33848Labels permutation156 permutation3
    mixedMoment B raw33848step0 raw33848step0Labels = mixedMoment B raw33848step1 raw33848step1Labels := by
      have ha : raw33848step1 = raw33848step0 := by apply Matrix.ext; unfold raw33848step1 raw33848step0; decide +kernel
      have hl : raw33848step0Labels = labelEmbedding6 ∘ raw33848step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33848step0 raw33848step0Labels raw33848step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw33849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33849step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33849step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33849 raw33849Labels = mixedMoment B node4217 node4217Labels := by
  calc
    mixedMoment B raw33849 raw33849Labels = mixedMoment B raw33849step0 raw33849step0Labels := by
      have ha : raw33849step0 = (fun i j => raw33849 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33849step0 raw33849; decide +kernel
      have hl : raw33849step0Labels = raw33849Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33849 raw33849Labels permutation160 permutation3
    mixedMoment B raw33849step0 raw33849step0Labels = mixedMoment B raw33849step1 raw33849step1Labels := by
      have ha : raw33849step1 = raw33849step0 := by apply Matrix.ext; unfold raw33849step1 raw33849step0; decide +kernel
      have hl : raw33849step0Labels = labelEmbedding6 ∘ raw33849step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33849step0 raw33849step0Labels raw33849step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4217 node4217Labels := by rfl

def raw33850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33850step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33850 raw33850Labels = mixedMoment B node4648 node4648Labels := by
  calc
    mixedMoment B raw33850 raw33850Labels = mixedMoment B raw33850step0 raw33850step0Labels := by
      have ha : raw33850step0 = (fun i j => raw33850 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33850step0 raw33850; decide +kernel
      have hl : raw33850step0Labels = raw33850Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33850 raw33850Labels permutation160 permutation3
    mixedMoment B raw33850step0 raw33850step0Labels = mixedMoment B raw33850step1 raw33850step1Labels := by
      have ha : raw33850step1 = raw33850step0 := by apply Matrix.ext; unfold raw33850step1 raw33850step0; decide +kernel
      have hl : raw33850step0Labels = labelEmbedding6 ∘ raw33850step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33850step0 raw33850step0Labels raw33850step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4648 node4648Labels := by rfl

def raw33851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33851step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33851 raw33851Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw33851 raw33851Labels = mixedMoment B raw33851step0 raw33851step0Labels := by
      have hz : ∀ j, raw33851 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33851step0 = (fun i j => raw33851 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33851step0 raw33851; decide +kernel
      have hl : raw33851step0Labels = raw33851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33851 raw33851Labels permutation520 hz
    mixedMoment B raw33851step0 raw33851step0Labels = mixedMoment B raw33851step1 raw33851step1Labels := by
      have ha : raw33851step1 = (fun i j => raw33851step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33851step1 raw33851step0; decide +kernel
      have hl : raw33851step1Labels = raw33851step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33851step0 raw33851step0Labels permutation34 permutation3
    mixedMoment B raw33851step1 raw33851step1Labels = mixedMoment B raw33851step2 raw33851step2Labels := by
      have ha : raw33851step2 = raw33851step1 := by apply Matrix.ext; unfold raw33851step2 raw33851step1; decide +kernel
      have hl : raw33851step1Labels = labelEmbedding6 ∘ raw33851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33851step1 raw33851step1Labels raw33851step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw33852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33852step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33852 raw33852Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw33852 raw33852Labels = mixedMoment B raw33852step0 raw33852step0Labels := by
      have ha : raw33852step0 = (fun i j => raw33852 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33852step0 raw33852; decide +kernel
      have hl : raw33852step0Labels = raw33852Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33852 raw33852Labels permutation173 permutation3
    mixedMoment B raw33852step0 raw33852step0Labels = mixedMoment B raw33852step1 raw33852step1Labels := by
      have ha : raw33852step1 = raw33852step0 := by apply Matrix.ext; unfold raw33852step1 raw33852step0; decide +kernel
      have hl : raw33852step0Labels = labelEmbedding6 ∘ raw33852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33852step0 raw33852step0Labels raw33852step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw33853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33853step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33853 raw33853Labels = mixedMoment B node4200 node4200Labels := by
  calc
    mixedMoment B raw33853 raw33853Labels = mixedMoment B raw33853step0 raw33853step0Labels := by
      have ha : raw33853step0 = (fun i j => raw33853 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33853step0 raw33853; decide +kernel
      have hl : raw33853step0Labels = raw33853Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33853 raw33853Labels permutation155 permutation3
    mixedMoment B raw33853step0 raw33853step0Labels = mixedMoment B raw33853step1 raw33853step1Labels := by
      have ha : raw33853step1 = raw33853step0 := by apply Matrix.ext; unfold raw33853step1 raw33853step0; decide +kernel
      have hl : raw33853step0Labels = labelEmbedding6 ∘ raw33853step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33853step0 raw33853step0Labels raw33853step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4200 node4200Labels := by rfl

def raw33854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33854step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33854 raw33854Labels = mixedMoment B node4634 node4634Labels := by
  calc
    mixedMoment B raw33854 raw33854Labels = mixedMoment B raw33854step0 raw33854step0Labels := by
      have ha : raw33854step0 = (fun i j => raw33854 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33854step0 raw33854; decide +kernel
      have hl : raw33854step0Labels = raw33854Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33854 raw33854Labels permutation155 permutation3
    mixedMoment B raw33854step0 raw33854step0Labels = mixedMoment B raw33854step1 raw33854step1Labels := by
      have ha : raw33854step1 = raw33854step0 := by apply Matrix.ext; unfold raw33854step1 raw33854step0; decide +kernel
      have hl : raw33854step0Labels = labelEmbedding6 ∘ raw33854step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33854step0 raw33854step0Labels raw33854step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4634 node4634Labels := by rfl

def raw33855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33855step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33855 raw33855Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw33855 raw33855Labels = mixedMoment B raw33855step0 raw33855step0Labels := by
      have ha : raw33855step0 = (fun i j => raw33855 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33855step0 raw33855; decide +kernel
      have hl : raw33855step0Labels = raw33855Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33855 raw33855Labels permutation155 permutation3
    mixedMoment B raw33855step0 raw33855step0Labels = mixedMoment B raw33855step1 raw33855step1Labels := by
      have ha : raw33855step1 = raw33855step0 := by apply Matrix.ext; unfold raw33855step1 raw33855step0; decide +kernel
      have hl : raw33855step0Labels = labelEmbedding6 ∘ raw33855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33855step0 raw33855step0Labels raw33855step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4766 node4766Labels := by rfl

def raw33856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33856step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33856 raw33856Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw33856 raw33856Labels = mixedMoment B raw33856step0 raw33856step0Labels := by
      have hz : ∀ j, raw33856 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33856step0 = (fun i j => raw33856 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33856step0 raw33856; decide +kernel
      have hl : raw33856step0Labels = raw33856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33856 raw33856Labels permutation520 hz
    mixedMoment B raw33856step0 raw33856step0Labels = mixedMoment B raw33856step1 raw33856step1Labels := by
      have ha : raw33856step1 = (fun i j => raw33856step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33856step1 raw33856step0; decide +kernel
      have hl : raw33856step1Labels = raw33856step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33856step0 raw33856step0Labels permutation33 permutation3
    mixedMoment B raw33856step1 raw33856step1Labels = mixedMoment B raw33856step2 raw33856step2Labels := by
      have ha : raw33856step2 = raw33856step1 := by apply Matrix.ext; unfold raw33856step2 raw33856step1; decide +kernel
      have hl : raw33856step1Labels = labelEmbedding6 ∘ raw33856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33856step1 raw33856step1Labels raw33856step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw33857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33857step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33857 raw33857Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw33857 raw33857Labels = mixedMoment B raw33857step0 raw33857step0Labels := by
      have ha : raw33857step0 = (fun i j => raw33857 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33857step0 raw33857; decide +kernel
      have hl : raw33857step0Labels = raw33857Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33857 raw33857Labels permutation157 permutation3
    mixedMoment B raw33857step0 raw33857step0Labels = mixedMoment B raw33857step1 raw33857step1Labels := by
      have ha : raw33857step1 = raw33857step0 := by apply Matrix.ext; unfold raw33857step1 raw33857step0; decide +kernel
      have hl : raw33857step0Labels = labelEmbedding6 ∘ raw33857step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33857step0 raw33857step0Labels raw33857step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw33858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33858step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33858 raw33858Labels = mixedMoment B node4199 node4199Labels := by
  calc
    mixedMoment B raw33858 raw33858Labels = mixedMoment B raw33858step0 raw33858step0Labels := by
      have ha : raw33858step0 = (fun i j => raw33858 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33858step0 raw33858; decide +kernel
      have hl : raw33858step0Labels = raw33858Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33858 raw33858Labels permutation152 permutation3
    mixedMoment B raw33858step0 raw33858step0Labels = mixedMoment B raw33858step1 raw33858step1Labels := by
      have ha : raw33858step1 = raw33858step0 := by apply Matrix.ext; unfold raw33858step1 raw33858step0; decide +kernel
      have hl : raw33858step0Labels = labelEmbedding6 ∘ raw33858step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33858step0 raw33858step0Labels raw33858step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4199 node4199Labels := by rfl

def raw33859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33859step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33859 raw33859Labels = mixedMoment B node4633 node4633Labels := by
  calc
    mixedMoment B raw33859 raw33859Labels = mixedMoment B raw33859step0 raw33859step0Labels := by
      have ha : raw33859step0 = (fun i j => raw33859 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33859step0 raw33859; decide +kernel
      have hl : raw33859step0Labels = raw33859Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33859 raw33859Labels permutation152 permutation3
    mixedMoment B raw33859step0 raw33859step0Labels = mixedMoment B raw33859step1 raw33859step1Labels := by
      have ha : raw33859step1 = raw33859step0 := by apply Matrix.ext; unfold raw33859step1 raw33859step0; decide +kernel
      have hl : raw33859step0Labels = labelEmbedding6 ∘ raw33859step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33859step0 raw33859step0Labels raw33859step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4633 node4633Labels := by rfl

def raw33860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33860step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33860 raw33860Labels = mixedMoment B node4764 node4764Labels := by
  calc
    mixedMoment B raw33860 raw33860Labels = mixedMoment B raw33860step0 raw33860step0Labels := by
      have ha : raw33860step0 = (fun i j => raw33860 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33860step0 raw33860; decide +kernel
      have hl : raw33860step0Labels = raw33860Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33860 raw33860Labels permutation152 permutation3
    mixedMoment B raw33860step0 raw33860step0Labels = mixedMoment B raw33860step1 raw33860step1Labels := by
      have ha : raw33860step1 = raw33860step0 := by apply Matrix.ext; unfold raw33860step1 raw33860step0; decide +kernel
      have hl : raw33860step0Labels = labelEmbedding6 ∘ raw33860step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33860step0 raw33860step0Labels raw33860step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4764 node4764Labels := by rfl

def raw33861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw33861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33861step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33861 raw33861Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw33861 raw33861Labels = mixedMoment B raw33861step0 raw33861step0Labels := by
      have hz : ∀ j, raw33861 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33861step0 = (fun i j => raw33861 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33861step0 raw33861; decide +kernel
      have hl : raw33861step0Labels = raw33861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33861 raw33861Labels permutation520 hz
    mixedMoment B raw33861step0 raw33861step0Labels = mixedMoment B raw33861step1 raw33861step1Labels := by
      have ha : raw33861step1 = (fun i j => raw33861step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33861step1 raw33861step0; decide +kernel
      have hl : raw33861step1Labels = raw33861step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33861step0 raw33861step0Labels permutation32 permutation3
    mixedMoment B raw33861step1 raw33861step1Labels = mixedMoment B raw33861step2 raw33861step2Labels := by
      have ha : raw33861step2 = raw33861step1 := by apply Matrix.ext; unfold raw33861step2 raw33861step1; decide +kernel
      have hl : raw33861step1Labels = labelEmbedding6 ∘ raw33861step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33861step1 raw33861step1Labels raw33861step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw33862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw33862step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33862step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33862step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33862 raw33862Labels = mixedMoment B node4409 node4409Labels := by
  calc
    mixedMoment B raw33862 raw33862Labels = mixedMoment B raw33862step0 raw33862step0Labels := by
      have ha : raw33862step0 = (fun i j => raw33862 (permutation173 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33862step0 raw33862; decide +kernel
      have hl : raw33862step0Labels = raw33862Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33862 raw33862Labels permutation173 permutation4
    mixedMoment B raw33862step0 raw33862step0Labels = mixedMoment B raw33862step1 raw33862step1Labels := by
      have ha : raw33862step1 = -raw33862step0 := by apply Matrix.ext; change ∀ i j, raw33862step1 i j = -(raw33862step0 i j); unfold raw33862step1 raw33862step0; decide +kernel
      have hl : raw33862step1Labels = raw33862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33862step1 raw33862step1Labels = mixedMoment B raw33862step2 raw33862step2Labels := by
      have ha : raw33862step2 = raw33862step1 := by apply Matrix.ext; unfold raw33862step2 raw33862step1; decide +kernel
      have hl : raw33862step1Labels = labelEmbedding7 ∘ raw33862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33862step1 raw33862step1Labels raw33862step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4409 node4409Labels := by rfl

def raw33863 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw33863step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33863step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33863step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33863 raw33863Labels = mixedMoment B node4746 node4746Labels := by
  calc
    mixedMoment B raw33863 raw33863Labels = mixedMoment B raw33863step0 raw33863step0Labels := by
      have ha : raw33863step0 = (fun i j => raw33863 (permutation173 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33863step0 raw33863; decide +kernel
      have hl : raw33863step0Labels = raw33863Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33863 raw33863Labels permutation173 permutation4
    mixedMoment B raw33863step0 raw33863step0Labels = mixedMoment B raw33863step1 raw33863step1Labels := by
      have ha : raw33863step1 = -raw33863step0 := by apply Matrix.ext; change ∀ i j, raw33863step1 i j = -(raw33863step0 i j); unfold raw33863step1 raw33863step0; decide +kernel
      have hl : raw33863step1Labels = raw33863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33863step1 raw33863step1Labels = mixedMoment B raw33863step2 raw33863step2Labels := by
      have ha : raw33863step2 = raw33863step1 := by apply Matrix.ext; unfold raw33863step2 raw33863step1; decide +kernel
      have hl : raw33863step1Labels = labelEmbedding7 ∘ raw33863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33863step1 raw33863step1Labels raw33863step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4746 node4746Labels := by rfl

def raw33864 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33864step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33864 raw33864Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw33864 raw33864Labels = mixedMoment B raw33864step0 raw33864step0Labels := by
      have ha : raw33864step0 = (fun i j => raw33864 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33864step0 raw33864; decide +kernel
      have hl : raw33864step0Labels = raw33864Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33864 raw33864Labels permutation154 permutation6
    mixedMoment B raw33864step0 raw33864step0Labels = mixedMoment B raw33864step1 raw33864step1Labels := by
      have ha : raw33864step1 = raw33864step0 := by apply Matrix.ext; unfold raw33864step1 raw33864step0; decide +kernel
      have hl : raw33864step0Labels = labelEmbedding9 ∘ raw33864step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33864step0 raw33864step0Labels raw33864step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw33865 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw33865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33865step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33865 raw33865Labels = mixedMoment B node4818 node4818Labels := by
  calc
    mixedMoment B raw33865 raw33865Labels = mixedMoment B raw33865step0 raw33865step0Labels := by
      have ha : raw33865step0 = (fun i j => raw33865 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33865step0 raw33865; decide +kernel
      have hl : raw33865step0Labels = raw33865Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33865 raw33865Labels permutation152 permutation6
    mixedMoment B raw33865step0 raw33865step0Labels = mixedMoment B raw33865step1 raw33865step1Labels := by
      have ha : raw33865step1 = raw33865step0 := by apply Matrix.ext; unfold raw33865step1 raw33865step0; decide +kernel
      have hl : raw33865step0Labels = labelEmbedding9 ∘ raw33865step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33865step0 raw33865step0Labels raw33865step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4818 node4818Labels := by rfl

def raw33866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw33866step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33866step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33866step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33866step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33866 raw33866Labels = mixedMoment B node4407 node4407Labels := by
  calc
    mixedMoment B raw33866 raw33866Labels = mixedMoment B raw33866step0 raw33866step0Labels := by
      have ha : raw33866step0 = (fun i j => raw33866 (permutation171 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33866step0 raw33866; decide +kernel
      have hl : raw33866step0Labels = raw33866Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33866 raw33866Labels permutation171 permutation4
    mixedMoment B raw33866step0 raw33866step0Labels = mixedMoment B raw33866step1 raw33866step1Labels := by
      have ha : raw33866step1 = -raw33866step0 := by apply Matrix.ext; change ∀ i j, raw33866step1 i j = -(raw33866step0 i j); unfold raw33866step1 raw33866step0; decide +kernel
      have hl : raw33866step1Labels = raw33866step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33866step1 raw33866step1Labels = mixedMoment B raw33866step2 raw33866step2Labels := by
      have ha : raw33866step2 = raw33866step1 := by apply Matrix.ext; unfold raw33866step2 raw33866step1; decide +kernel
      have hl : raw33866step1Labels = labelEmbedding7 ∘ raw33866step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33866step1 raw33866step1Labels raw33866step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4407 node4407Labels := by rfl

def raw33867 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33867step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33867 raw33867Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw33867 raw33867Labels = mixedMoment B raw33867step0 raw33867step0Labels := by
      have ha : raw33867step0 = (fun i j => raw33867 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33867step0 raw33867; decide +kernel
      have hl : raw33867step0Labels = raw33867Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33867 raw33867Labels permutation154 permutation6
    mixedMoment B raw33867step0 raw33867step0Labels = mixedMoment B raw33867step1 raw33867step1Labels := by
      have ha : raw33867step1 = raw33867step0 := by apply Matrix.ext; unfold raw33867step1 raw33867step0; decide +kernel
      have hl : raw33867step0Labels = labelEmbedding9 ∘ raw33867step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33867step0 raw33867step0Labels raw33867step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw33868 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33868step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33868 raw33868Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw33868 raw33868Labels = mixedMoment B raw33868step0 raw33868step0Labels := by
      have ha : raw33868step0 = (fun i j => raw33868 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33868step0 raw33868; decide +kernel
      have hl : raw33868step0Labels = raw33868Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33868 raw33868Labels permutation154 permutation6
    mixedMoment B raw33868step0 raw33868step0Labels = mixedMoment B raw33868step1 raw33868step1Labels := by
      have ha : raw33868step1 = raw33868step0 := by apply Matrix.ext; unfold raw33868step1 raw33868step0; decide +kernel
      have hl : raw33868step0Labels = labelEmbedding9 ∘ raw33868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33868step0 raw33868step0Labels raw33868step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw33869 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw33869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33869step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33869 raw33869Labels = mixedMoment B node4806 node4806Labels := by
  calc
    mixedMoment B raw33869 raw33869Labels = mixedMoment B raw33869step0 raw33869step0Labels := by
      have ha : raw33869step0 = (fun i j => raw33869 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33869step0 raw33869; decide +kernel
      have hl : raw33869step0Labels = raw33869Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33869 raw33869Labels permutation154 permutation6
    mixedMoment B raw33869step0 raw33869step0Labels = mixedMoment B raw33869step1 raw33869step1Labels := by
      have ha : raw33869step1 = raw33869step0 := by apply Matrix.ext; unfold raw33869step1 raw33869step0; decide +kernel
      have hl : raw33869step0Labels = labelEmbedding9 ∘ raw33869step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33869step0 raw33869step0Labels raw33869step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4806 node4806Labels := by rfl

def raw33870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw33870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw33870step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33870step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33870step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33870 raw33870Labels = mixedMoment B node4407 node4407Labels := by
  calc
    mixedMoment B raw33870 raw33870Labels = mixedMoment B raw33870step0 raw33870step0Labels := by
      have ha : raw33870step0 = (fun i j => raw33870 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33870step0 raw33870; decide +kernel
      have hl : raw33870step0Labels = raw33870Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33870 raw33870Labels permutation170 permutation4
    mixedMoment B raw33870step0 raw33870step0Labels = mixedMoment B raw33870step1 raw33870step1Labels := by
      have ha : raw33870step1 = -raw33870step0 := by apply Matrix.ext; change ∀ i j, raw33870step1 i j = -(raw33870step0 i j); unfold raw33870step1 raw33870step0; decide +kernel
      have hl : raw33870step1Labels = raw33870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33870step1 raw33870step1Labels = mixedMoment B raw33870step2 raw33870step2Labels := by
      have ha : raw33870step2 = raw33870step1 := by apply Matrix.ext; unfold raw33870step2 raw33870step1; decide +kernel
      have hl : raw33870step1Labels = labelEmbedding7 ∘ raw33870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33870step1 raw33870step1Labels raw33870step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4407 node4407Labels := by rfl

def raw33871 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw33871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33871step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33871 raw33871Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw33871 raw33871Labels = mixedMoment B raw33871step0 raw33871step0Labels := by
      have ha : raw33871step0 = (fun i j => raw33871 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33871step0 raw33871; decide +kernel
      have hl : raw33871step0Labels = raw33871Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33871 raw33871Labels permutation152 permutation6
    mixedMoment B raw33871step0 raw33871step0Labels = mixedMoment B raw33871step1 raw33871step1Labels := by
      have ha : raw33871step1 = raw33871step0 := by apply Matrix.ext; unfold raw33871step1 raw33871step0; decide +kernel
      have hl : raw33871step0Labels = labelEmbedding9 ∘ raw33871step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33871step0 raw33871step0Labels raw33871step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw33872 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw33872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33872step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33872 raw33872Labels = mixedMoment B node4806 node4806Labels := by
  calc
    mixedMoment B raw33872 raw33872Labels = mixedMoment B raw33872step0 raw33872step0Labels := by
      have ha : raw33872step0 = (fun i j => raw33872 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33872step0 raw33872; decide +kernel
      have hl : raw33872step0Labels = raw33872Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33872 raw33872Labels permutation152 permutation6
    mixedMoment B raw33872step0 raw33872step0Labels = mixedMoment B raw33872step1 raw33872step1Labels := by
      have ha : raw33872step1 = raw33872step0 := by apply Matrix.ext; unfold raw33872step1 raw33872step0; decide +kernel
      have hl : raw33872step0Labels = labelEmbedding9 ∘ raw33872step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33872step0 raw33872step0Labels raw33872step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4806 node4806Labels := by rfl

def raw33873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33873step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33873step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33873step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33873 raw33873Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw33873 raw33873Labels = mixedMoment B raw33873step0 raw33873step0Labels := by
      have ha : raw33873step0 = (fun i j => raw33873 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33873step0 raw33873; decide +kernel
      have hl : raw33873step0Labels = raw33873Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33873 raw33873Labels permutation152 permutation4
    mixedMoment B raw33873step0 raw33873step0Labels = mixedMoment B raw33873step1 raw33873step1Labels := by
      have ha : raw33873step1 = -raw33873step0 := by apply Matrix.ext; change ∀ i j, raw33873step1 i j = -(raw33873step0 i j); unfold raw33873step1 raw33873step0; decide +kernel
      have hl : raw33873step1Labels = raw33873step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33873step1 raw33873step1Labels = mixedMoment B raw33873step2 raw33873step2Labels := by
      have ha : raw33873step2 = raw33873step1 := by apply Matrix.ext; unfold raw33873step2 raw33873step1; decide +kernel
      have hl : raw33873step1Labels = labelEmbedding7 ∘ raw33873step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33873step1 raw33873step1Labels raw33873step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw33874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33874step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33874step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33874step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33874 raw33874Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw33874 raw33874Labels = mixedMoment B raw33874step0 raw33874step0Labels := by
      have ha : raw33874step0 = (fun i j => raw33874 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33874step0 raw33874; decide +kernel
      have hl : raw33874step0Labels = raw33874Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33874 raw33874Labels permutation164 permutation7
    mixedMoment B raw33874step0 raw33874step0Labels = mixedMoment B raw33874step1 raw33874step1Labels := by
      have ha : raw33874step1 = -raw33874step0 := by apply Matrix.ext; change ∀ i j, raw33874step1 i j = -(raw33874step0 i j); unfold raw33874step1 raw33874step0; decide +kernel
      have hl : raw33874step1Labels = raw33874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33874step1 raw33874step1Labels = mixedMoment B raw33874step2 raw33874step2Labels := by
      have ha : raw33874step2 = raw33874step1 := by apply Matrix.ext; unfold raw33874step2 raw33874step1; decide +kernel
      have hl : raw33874step1Labels = labelEmbedding10 ∘ raw33874step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33874step1 raw33874step1Labels raw33874step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw33875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33875step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33875step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33875step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33875 raw33875Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw33875 raw33875Labels = mixedMoment B raw33875step0 raw33875step0Labels := by
      have ha : raw33875step0 = (fun i j => raw33875 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33875step0 raw33875; decide +kernel
      have hl : raw33875step0Labels = raw33875Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33875 raw33875Labels permutation164 permutation7
    mixedMoment B raw33875step0 raw33875step0Labels = mixedMoment B raw33875step1 raw33875step1Labels := by
      have ha : raw33875step1 = -raw33875step0 := by apply Matrix.ext; change ∀ i j, raw33875step1 i j = -(raw33875step0 i j); unfold raw33875step1 raw33875step0; decide +kernel
      have hl : raw33875step1Labels = raw33875step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33875step1 raw33875step1Labels = mixedMoment B raw33875step2 raw33875step2Labels := by
      have ha : raw33875step2 = raw33875step1 := by apply Matrix.ext; unfold raw33875step2 raw33875step1; decide +kernel
      have hl : raw33875step1Labels = labelEmbedding10 ∘ raw33875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33875step1 raw33875step1Labels raw33875step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw33876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33876step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33876step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33876step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33876 raw33876Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw33876 raw33876Labels = mixedMoment B raw33876step0 raw33876step0Labels := by
      have ha : raw33876step0 = (fun i j => raw33876 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33876step0 raw33876; decide +kernel
      have hl : raw33876step0Labels = raw33876Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33876 raw33876Labels permutation164 permutation7
    mixedMoment B raw33876step0 raw33876step0Labels = mixedMoment B raw33876step1 raw33876step1Labels := by
      have ha : raw33876step1 = -raw33876step0 := by apply Matrix.ext; change ∀ i j, raw33876step1 i j = -(raw33876step0 i j); unfold raw33876step1 raw33876step0; decide +kernel
      have hl : raw33876step1Labels = raw33876step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33876step1 raw33876step1Labels = mixedMoment B raw33876step2 raw33876step2Labels := by
      have ha : raw33876step2 = raw33876step1 := by apply Matrix.ext; unfold raw33876step2 raw33876step1; decide +kernel
      have hl : raw33876step1Labels = labelEmbedding10 ∘ raw33876step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33876step1 raw33876step1Labels raw33876step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw33877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33877step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33877step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33877 raw33877Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw33877 raw33877Labels = mixedMoment B raw33877step0 raw33877step0Labels := by
      have hz : ∀ j, raw33877 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33877step0 = (fun i j => raw33877 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33877step0 raw33877; decide +kernel
      have hl : raw33877step0Labels = raw33877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33877 raw33877Labels permutation520 hz
    mixedMoment B raw33877step0 raw33877step0Labels = mixedMoment B raw33877step1 raw33877step1Labels := by
      have ha : raw33877step1 = (fun i j => raw33877step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33877step1 raw33877step0; decide +kernel
      have hl : raw33877step1Labels = raw33877step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33877step0 raw33877step0Labels permutation32 permutation7
    mixedMoment B raw33877step1 raw33877step1Labels = mixedMoment B raw33877step2 raw33877step2Labels := by
      have ha : raw33877step2 = -raw33877step1 := by apply Matrix.ext; change ∀ i j, raw33877step2 i j = -(raw33877step1 i j); unfold raw33877step2 raw33877step1; decide +kernel
      have hl : raw33877step2Labels = raw33877step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33877step2 raw33877step2Labels = mixedMoment B raw33877step3 raw33877step3Labels := by
      have ha : raw33877step3 = raw33877step2 := by apply Matrix.ext; unfold raw33877step3 raw33877step2; decide +kernel
      have hl : raw33877step2Labels = labelEmbedding10 ∘ raw33877step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33877step2 raw33877step2Labels raw33877step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw33878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33878step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33878step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33878step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33878step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33878 raw33878Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw33878 raw33878Labels = mixedMoment B raw33878step0 raw33878step0Labels := by
      have ha : raw33878step0 = (fun i j => raw33878 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33878step0 raw33878; decide +kernel
      have hl : raw33878step0Labels = raw33878Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33878 raw33878Labels permutation164 permutation7
    mixedMoment B raw33878step0 raw33878step0Labels = mixedMoment B raw33878step1 raw33878step1Labels := by
      have ha : raw33878step1 = -raw33878step0 := by apply Matrix.ext; change ∀ i j, raw33878step1 i j = -(raw33878step0 i j); unfold raw33878step1 raw33878step0; decide +kernel
      have hl : raw33878step1Labels = raw33878step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33878step1 raw33878step1Labels = mixedMoment B raw33878step2 raw33878step2Labels := by
      have ha : raw33878step2 = raw33878step1 := by apply Matrix.ext; unfold raw33878step2 raw33878step1; decide +kernel
      have hl : raw33878step1Labels = labelEmbedding10 ∘ raw33878step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33878step1 raw33878step1Labels raw33878step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw33879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33879 raw33879Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw33879 raw33879Labels = mixedMoment B raw33879step0 raw33879step0Labels := by
      have hz : ∀ j, raw33879 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33879step0 = (fun i j => raw33879 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33879step0 raw33879; decide +kernel
      have hl : raw33879step0Labels = raw33879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33879 raw33879Labels permutation265 hz
    mixedMoment B raw33879step0 raw33879step0Labels = mixedMoment B raw33879step1 raw33879step1Labels := by
      have ha : raw33879step1 = (fun i j => raw33879step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33879step1 raw33879step0; decide +kernel
      have hl : raw33879step1Labels = raw33879step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33879step0 raw33879step0Labels permutation34 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw33880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33880 raw33880Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw33880 raw33880Labels = mixedMoment B raw33880step0 raw33880step0Labels := by
      have hz : ∀ j, raw33880 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33880step0 = (fun i j => raw33880 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33880step0 raw33880; decide +kernel
      have hl : raw33880step0Labels = raw33880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33880 raw33880Labels permutation265 hz
    mixedMoment B raw33880step0 raw33880step0Labels = mixedMoment B raw33880step1 raw33880step1Labels := by
      have ha : raw33880step1 = (fun i j => raw33880step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33880step1 raw33880step0; decide +kernel
      have hl : raw33880step1Labels = raw33880step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33880step0 raw33880step0Labels permutation34 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw33881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33881 raw33881Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw33881 raw33881Labels = mixedMoment B raw33881step0 raw33881step0Labels := by
      have hz : ∀ j, raw33881 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33881step0 = (fun i j => raw33881 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33881step0 raw33881; decide +kernel
      have hl : raw33881step0Labels = raw33881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33881 raw33881Labels permutation265 hz
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw33882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33882 raw33882Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw33882 raw33882Labels = mixedMoment B raw33882step0 raw33882step0Labels := by
      have hz : ∀ j, raw33882 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33882step0 = (fun i j => raw33882 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33882step0 raw33882; decide +kernel
      have hl : raw33882step0Labels = raw33882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33882 raw33882Labels permutation520 hz
    mixedMoment B raw33882step0 raw33882step0Labels = mixedMoment B raw33882step1 raw33882step1Labels := by
      have hz : ∀ j, raw33882step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw33882step1 = (fun i j => raw33882step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw33882step1 raw33882step0; decide +kernel
      have hl : raw33882step1Labels = raw33882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33882step0 raw33882step0Labels permutation56 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw33883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33883 raw33883Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw33883 raw33883Labels = mixedMoment B raw33883step0 raw33883step0Labels := by
      have hz : ∀ j, raw33883 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33883step0 = (fun i j => raw33883 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33883step0 raw33883; decide +kernel
      have hl : raw33883step0Labels = raw33883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33883 raw33883Labels permutation265 hz
    mixedMoment B raw33883step0 raw33883step0Labels = mixedMoment B raw33883step1 raw33883step1Labels := by
      have ha : raw33883step1 = (fun i j => raw33883step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33883step1 raw33883step0; decide +kernel
      have hl : raw33883step1Labels = raw33883step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33883step0 raw33883step0Labels permutation34 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw33884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33884 raw33884Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw33884 raw33884Labels = mixedMoment B raw33884step0 raw33884step0Labels := by
      have ha : raw33884step0 = (fun i j => raw33884 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33884step0 raw33884; decide +kernel
      have hl : raw33884step0Labels = raw33884Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33884 raw33884Labels permutation164 permutation2
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw33885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33885 raw33885Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw33885 raw33885Labels = mixedMoment B raw33885step0 raw33885step0Labels := by
      have ha : raw33885step0 = (fun i j => raw33885 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33885step0 raw33885; decide +kernel
      have hl : raw33885step0Labels = raw33885Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33885 raw33885Labels permutation164 permutation2
    _ = mixedMoment B node4679 node4679Labels := by rfl

def raw33886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33886 raw33886Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw33886 raw33886Labels = mixedMoment B raw33886step0 raw33886step0Labels := by
      have ha : raw33886step0 = (fun i j => raw33886 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33886step0 raw33886; decide +kernel
      have hl : raw33886step0Labels = raw33886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33886 raw33886Labels permutation160 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw33887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33887 raw33887Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw33887 raw33887Labels = mixedMoment B raw33887step0 raw33887step0Labels := by
      have hz : ∀ j, raw33887 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33887step0 = (fun i j => raw33887 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33887step0 raw33887; decide +kernel
      have hl : raw33887step0Labels = raw33887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33887 raw33887Labels permutation520 hz
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw33888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33888 raw33888Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw33888 raw33888Labels = mixedMoment B raw33888step0 raw33888step0Labels := by
      have ha : raw33888step0 = (fun i j => raw33888 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33888step0 raw33888; decide +kernel
      have hl : raw33888step0Labels = raw33888Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33888 raw33888Labels permutation164 permutation2
    _ = mixedMoment B node4833 node4833Labels := by rfl

def raw33889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33889 raw33889Labels = mixedMoment B node4329 node4329Labels := by
  calc
    mixedMoment B raw33889 raw33889Labels = mixedMoment B raw33889step0 raw33889step0Labels := by
      have ha : raw33889step0 = (fun i j => raw33889 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33889step0 raw33889; decide +kernel
      have hl : raw33889step0Labels = raw33889Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33889 raw33889Labels permutation154 permutation2
    _ = mixedMoment B node4329 node4329Labels := by rfl

def raw33890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33890 raw33890Labels = mixedMoment B node4666 node4666Labels := by
  calc
    mixedMoment B raw33890 raw33890Labels = mixedMoment B raw33890step0 raw33890step0Labels := by
      have ha : raw33890step0 = (fun i j => raw33890 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33890step0 raw33890; decide +kernel
      have hl : raw33890step0Labels = raw33890Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33890 raw33890Labels permutation154 permutation2
    _ = mixedMoment B node4666 node4666Labels := by rfl

def raw33891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33891 raw33891Labels = mixedMoment B node4774 node4774Labels := by
  calc
    mixedMoment B raw33891 raw33891Labels = mixedMoment B raw33891step0 raw33891step0Labels := by
      have ha : raw33891step0 = (fun i j => raw33891 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33891step0 raw33891; decide +kernel
      have hl : raw33891step0Labels = raw33891Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33891 raw33891Labels permutation154 permutation2
    _ = mixedMoment B node4774 node4774Labels := by rfl

def raw33892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33892 raw33892Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw33892 raw33892Labels = mixedMoment B raw33892step0 raw33892step0Labels := by
      have hz : ∀ j, raw33892 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33892step0 = (fun i j => raw33892 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33892step0 raw33892; decide +kernel
      have hl : raw33892step0Labels = raw33892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33892 raw33892Labels permutation520 hz
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw33893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33893 raw33893Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw33893 raw33893Labels = mixedMoment B raw33893step0 raw33893step0Labels := by
      have ha : raw33893step0 = (fun i j => raw33893 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33893step0 raw33893; decide +kernel
      have hl : raw33893step0Labels = raw33893Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33893 raw33893Labels permutation155 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw33894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33894 raw33894Labels = mixedMoment B node4332 node4332Labels := by
  calc
    _ = mixedMoment B node4332 node4332Labels := by rfl

def raw33895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33895 raw33895Labels = mixedMoment B node4668 node4668Labels := by
  calc
    _ = mixedMoment B node4668 node4668Labels := by rfl

def raw33896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33896 raw33896Labels = mixedMoment B node4775 node4775Labels := by
  calc
    _ = mixedMoment B node4775 node4775Labels := by rfl

def raw33897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33897 raw33897Labels = mixedMoment B node4795 node4795Labels := by
  calc
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw33898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33898 raw33898Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw33898 raw33898Labels = mixedMoment B raw33898step0 raw33898step0Labels := by
      have ha : raw33898step0 = (fun i j => raw33898 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33898step0 raw33898; decide +kernel
      have hl : raw33898step0Labels = raw33898Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33898 raw33898Labels permutation153 permutation2
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw33899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33899 raw33899Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw33899 raw33899Labels = mixedMoment B raw33899step0 raw33899step0Labels := by
      have ha : raw33899step0 = (fun i j => raw33899 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33899step0 raw33899; decide +kernel
      have hl : raw33899step0Labels = raw33899Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33899 raw33899Labels permutation154 permutation2
    _ = mixedMoment B node4327 node4327Labels := by rfl

def raw33900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33900 raw33900Labels = mixedMoment B node4664 node4664Labels := by
  calc
    mixedMoment B raw33900 raw33900Labels = mixedMoment B raw33900step0 raw33900step0Labels := by
      have ha : raw33900step0 = (fun i j => raw33900 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33900step0 raw33900; decide +kernel
      have hl : raw33900step0Labels = raw33900Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33900 raw33900Labels permutation154 permutation2
    _ = mixedMoment B node4664 node4664Labels := by rfl

def raw33901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33901 raw33901Labels = mixedMoment B node4772 node4772Labels := by
  calc
    mixedMoment B raw33901 raw33901Labels = mixedMoment B raw33901step0 raw33901step0Labels := by
      have ha : raw33901step0 = (fun i j => raw33901 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33901step0 raw33901; decide +kernel
      have hl : raw33901step0Labels = raw33901Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33901 raw33901Labels permutation154 permutation2
    _ = mixedMoment B node4772 node4772Labels := by rfl

def raw33902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33902 raw33902Labels = mixedMoment B node4792 node4792Labels := by
  calc
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw33903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33903 raw33903Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw33903 raw33903Labels = mixedMoment B raw33903step0 raw33903step0Labels := by
      have hz : ∀ j, raw33903 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33903step0 = (fun i j => raw33903 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33903step0 raw33903; decide +kernel
      have hl : raw33903step0Labels = raw33903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33903 raw33903Labels permutation520 hz
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw33904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33904 raw33904Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw33904 raw33904Labels = mixedMoment B raw33904step0 raw33904step0Labels := by
      have ha : raw33904step0 = (fun i j => raw33904 (permutation229 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33904step0 raw33904; decide +kernel
      have hl : raw33904step0Labels = raw33904Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33904 raw33904Labels permutation229 permutation6
    mixedMoment B raw33904step0 raw33904step0Labels = mixedMoment B raw33904step1 raw33904step1Labels := by
      have ha : raw33904step1 = -raw33904step0 := by apply Matrix.ext; change ∀ i j, raw33904step1 i j = -(raw33904step0 i j); unfold raw33904step1 raw33904step0; decide +kernel
      have hl : raw33904step1Labels = raw33904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3091 node3091Labels := by rfl

def raw33905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33905 raw33905Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw33905 raw33905Labels = mixedMoment B raw33905step0 raw33905step0Labels := by
      have ha : raw33905step0 = (fun i j => raw33905 (permutation229 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33905step0 raw33905; decide +kernel
      have hl : raw33905step0Labels = raw33905Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33905 raw33905Labels permutation229 permutation6
    mixedMoment B raw33905step0 raw33905step0Labels = mixedMoment B raw33905step1 raw33905step1Labels := by
      have ha : raw33905step1 = -raw33905step0 := by apply Matrix.ext; change ∀ i j, raw33905step1 i j = -(raw33905step0 i j); unfold raw33905step1 raw33905step0; decide +kernel
      have hl : raw33905step1Labels = raw33905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3084 node3084Labels := by rfl

def raw33906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33906 raw33906Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw33906 raw33906Labels = mixedMoment B raw33906step0 raw33906step0Labels := by
      have ha : raw33906step0 = (fun i j => raw33906 (permutation228 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33906step0 raw33906; decide +kernel
      have hl : raw33906step0Labels = raw33906Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33906 raw33906Labels permutation228 permutation6
    mixedMoment B raw33906step0 raw33906step0Labels = mixedMoment B raw33906step1 raw33906step1Labels := by
      have ha : raw33906step1 = -raw33906step0 := by apply Matrix.ext; change ∀ i j, raw33906step1 i j = -(raw33906step0 i j); unfold raw33906step1 raw33906step0; decide +kernel
      have hl : raw33906step1Labels = raw33906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw33907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33907 raw33907Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw33907 raw33907Labels = mixedMoment B raw33907step0 raw33907step0Labels := by
      have hz : ∀ j, raw33907 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33907step0 = (fun i j => raw33907 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33907step0 raw33907; decide +kernel
      have hl : raw33907step0Labels = raw33907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33907 raw33907Labels permutation520 hz
    mixedMoment B raw33907step0 raw33907step0Labels = mixedMoment B raw33907step1 raw33907step1Labels := by
      have ha : raw33907step1 = (fun i j => raw33907step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33907step1 raw33907step0; decide +kernel
      have hl : raw33907step1Labels = raw33907step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33907step0 raw33907step0Labels permutation37 permutation6
    mixedMoment B raw33907step1 raw33907step1Labels = mixedMoment B raw33907step2 raw33907step2Labels := by
      have ha : raw33907step2 = -raw33907step1 := by apply Matrix.ext; change ∀ i j, raw33907step2 i j = -(raw33907step1 i j); unfold raw33907step2 raw33907step1; decide +kernel
      have hl : raw33907step2Labels = raw33907step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw33908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw33908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33908 raw33908Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw33908 raw33908Labels = mixedMoment B raw33908step0 raw33908step0Labels := by
      have ha : raw33908step0 = (fun i j => raw33908 (permutation227 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33908step0 raw33908; decide +kernel
      have hl : raw33908step0Labels = raw33908Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33908 raw33908Labels permutation227 permutation6
    mixedMoment B raw33908step0 raw33908step0Labels = mixedMoment B raw33908step1 raw33908step1Labels := by
      have ha : raw33908step1 = -raw33908step0 := by apply Matrix.ext; change ∀ i j, raw33908step1 i j = -(raw33908step0 i j); unfold raw33908step1 raw33908step0; decide +kernel
      have hl : raw33908step1Labels = raw33908step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw33909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33909 raw33909Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw33909 raw33909Labels = mixedMoment B raw33909step0 raw33909step0Labels := by
      have hz : ∀ j, raw33909 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33909step0 = (fun i j => raw33909 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33909step0 raw33909; decide +kernel
      have hl : raw33909step0Labels = raw33909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33909 raw33909Labels permutation265 hz
    mixedMoment B raw33909step0 raw33909step0Labels = mixedMoment B raw33909step1 raw33909step1Labels := by
      have ha : raw33909step1 = (fun i j => raw33909step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33909step1 raw33909step0; decide +kernel
      have hl : raw33909step1Labels = raw33909step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33909step0 raw33909step0Labels permutation32 permutation3
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw33910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33910 raw33910Labels = mixedMoment B node3184 node3184Labels := by
  calc
    mixedMoment B raw33910 raw33910Labels = mixedMoment B raw33910step0 raw33910step0Labels := by
      have hz : ∀ j, raw33910 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33910step0 = (fun i j => raw33910 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33910step0 raw33910; decide +kernel
      have hl : raw33910step0Labels = raw33910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33910 raw33910Labels permutation265 hz
    mixedMoment B raw33910step0 raw33910step0Labels = mixedMoment B raw33910step1 raw33910step1Labels := by
      have ha : raw33910step1 = (fun i j => raw33910step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33910step1 raw33910step0; decide +kernel
      have hl : raw33910step1Labels = raw33910step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33910step0 raw33910step0Labels permutation32 permutation3
    _ = mixedMoment B node3184 node3184Labels := by rfl

def raw33911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33911step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33911 raw33911Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw33911 raw33911Labels = mixedMoment B raw33911step0 raw33911step0Labels := by
      have hz : ∀ j, raw33911 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33911step0 = (fun i j => raw33911 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33911step0 raw33911; decide +kernel
      have hl : raw33911step0Labels = raw33911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33911 raw33911Labels permutation265 hz
    mixedMoment B raw33911step0 raw33911step0Labels = mixedMoment B raw33911step1 raw33911step1Labels := by
      have ha : raw33911step1 = (fun i j => raw33911step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33911step1 raw33911step0; decide +kernel
      have hl : raw33911step1Labels = raw33911step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33911step0 raw33911step0Labels permutation32 permutation3
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw33912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33912step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw33912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33912 raw33912Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw33912 raw33912Labels = mixedMoment B raw33912step0 raw33912step0Labels := by
      have hz : ∀ j, raw33912 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33912step0 = (fun i j => raw33912 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33912step0 raw33912; decide +kernel
      have hl : raw33912step0Labels = raw33912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33912 raw33912Labels permutation520 hz
    mixedMoment B raw33912step0 raw33912step0Labels = mixedMoment B raw33912step1 raw33912step1Labels := by
      have hz : ∀ j, raw33912step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw33912step1 = (fun i j => raw33912step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw33912step1 raw33912step0; decide +kernel
      have hl : raw33912step1Labels = raw33912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33912step0 raw33912step0Labels permutation56 hz
    mixedMoment B raw33912step1 raw33912step1Labels = mixedMoment B raw33912step2 raw33912step2Labels := by
      have ha : raw33912step2 = (fun i j => raw33912step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33912step2 raw33912step1; decide +kernel
      have hl : raw33912step2Labels = raw33912step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33912step1 raw33912step1Labels permutation8 permutation3
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw33913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33913 raw33913Labels = mixedMoment B node3228 node3228Labels := by
  calc
    mixedMoment B raw33913 raw33913Labels = mixedMoment B raw33913step0 raw33913step0Labels := by
      have hz : ∀ j, raw33913 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33913step0 = (fun i j => raw33913 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33913step0 raw33913; decide +kernel
      have hl : raw33913step0Labels = raw33913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33913 raw33913Labels permutation265 hz
    mixedMoment B raw33913step0 raw33913step0Labels = mixedMoment B raw33913step1 raw33913step1Labels := by
      have ha : raw33913step1 = (fun i j => raw33913step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33913step1 raw33913step0; decide +kernel
      have hl : raw33913step1Labels = raw33913step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33913step0 raw33913step0Labels permutation33 permutation3
    _ = mixedMoment B node3228 node3228Labels := by rfl

def raw33914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33914 raw33914Labels = mixedMoment B node1339 node1339Labels := by
  calc
    mixedMoment B raw33914 raw33914Labels = mixedMoment B raw33914step0 raw33914step0Labels := by
      have ha : raw33914step0 = (fun i j => raw33914 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33914step0 raw33914; decide +kernel
      have hl : raw33914step0Labels = raw33914Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33914 raw33914Labels permutation152 permutation3
    _ = mixedMoment B node1339 node1339Labels := by rfl

def raw33915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33915 raw33915Labels = mixedMoment B node3139 node3139Labels := by
  calc
    mixedMoment B raw33915 raw33915Labels = mixedMoment B raw33915step0 raw33915step0Labels := by
      have ha : raw33915step0 = (fun i j => raw33915 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33915step0 raw33915; decide +kernel
      have hl : raw33915step0Labels = raw33915Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33915 raw33915Labels permutation152 permutation3
    _ = mixedMoment B node3139 node3139Labels := by rfl

def raw33916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33916 raw33916Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw33916 raw33916Labels = mixedMoment B raw33916step0 raw33916step0Labels := by
      have ha : raw33916step0 = (fun i j => raw33916 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33916step0 raw33916; decide +kernel
      have hl : raw33916step0Labels = raw33916Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33916 raw33916Labels permutation158 permutation3
    _ = mixedMoment B node3204 node3204Labels := by rfl

def raw33917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw33917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33917 raw33917Labels = mixedMoment B node3213 node3213Labels := by
  calc
    mixedMoment B raw33917 raw33917Labels = mixedMoment B raw33917step0 raw33917step0Labels := by
      have hz : ∀ j, raw33917 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33917step0 = (fun i j => raw33917 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33917step0 raw33917; decide +kernel
      have hl : raw33917step0Labels = raw33917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33917 raw33917Labels permutation520 hz
    mixedMoment B raw33917step0 raw33917step0Labels = mixedMoment B raw33917step1 raw33917step1Labels := by
      have ha : raw33917step1 = (fun i j => raw33917step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33917step1 raw33917step0; decide +kernel
      have hl : raw33917step1Labels = raw33917step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33917step0 raw33917step0Labels permutation32 permutation3
    _ = mixedMoment B node3213 node3213Labels := by rfl

def raw33918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33918 raw33918Labels = mixedMoment B node3212 node3212Labels := by
  calc
    mixedMoment B raw33918 raw33918Labels = mixedMoment B raw33918step0 raw33918step0Labels := by
      have ha : raw33918step0 = (fun i j => raw33918 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33918step0 raw33918; decide +kernel
      have hl : raw33918step0Labels = raw33918Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33918 raw33918Labels permutation153 permutation3
    _ = mixedMoment B node3212 node3212Labels := by rfl

def raw33919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33919 raw33919Labels = mixedMoment B node1331 node1331Labels := by
  calc
    mixedMoment B raw33919 raw33919Labels = mixedMoment B raw33919step0 raw33919step0Labels := by
      have ha : raw33919step0 = (fun i j => raw33919 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33919step0 raw33919; decide +kernel
      have hl : raw33919step0Labels = raw33919Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33919 raw33919Labels permutation154 permutation3
    _ = mixedMoment B node1331 node1331Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
