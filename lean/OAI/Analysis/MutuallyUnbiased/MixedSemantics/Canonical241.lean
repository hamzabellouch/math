import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, 0, -2], ![2, -2, 0]]
def raw30848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30848 raw30848Labels = mixedMoment B node2394 node2394Labels := by
  calc
    mixedMoment B raw30848 raw30848Labels = mixedMoment B raw30848step0 raw30848step0Labels := by
      have hz : ∀ j, raw30848 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30848step0 = (fun i j => raw30848 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30848step0 raw30848; decide +kernel
      have hl : raw30848step0Labels = raw30848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30848 raw30848Labels permutation434 hz
    mixedMoment B raw30848step0 raw30848step0Labels = mixedMoment B raw30848step1 raw30848step1Labels := by
      have ha : raw30848step1 = (fun i j => raw30848step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30848step1 raw30848step0; decide +kernel
      have hl : raw30848step1Labels = raw30848step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30848step0 raw30848step0Labels permutation33 permutation2
    _ = mixedMoment B node2394 node2394Labels := by rfl

def raw30849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, 0, -2], ![2, -2, 0]]
def raw30849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30849 raw30849Labels = mixedMoment B node3660 node3660Labels := by
  calc
    mixedMoment B raw30849 raw30849Labels = mixedMoment B raw30849step0 raw30849step0Labels := by
      have hz : ∀ j, raw30849 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30849step0 = (fun i j => raw30849 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30849step0 raw30849; decide +kernel
      have hl : raw30849step0Labels = raw30849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30849 raw30849Labels permutation434 hz
    mixedMoment B raw30849step0 raw30849step0Labels = mixedMoment B raw30849step1 raw30849step1Labels := by
      have ha : raw30849step1 = (fun i j => raw30849step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30849step1 raw30849step0; decide +kernel
      have hl : raw30849step1Labels = raw30849step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30849step0 raw30849step0Labels permutation33 permutation2
    _ = mixedMoment B node3660 node3660Labels := by rfl

def raw30850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 3, -2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 3, -2], ![2, 0, -2], ![2, -2, 0]]
def raw30850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw30850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30850 raw30850Labels = mixedMoment B node2679 node2679Labels := by
  calc
    mixedMoment B raw30850 raw30850Labels = mixedMoment B raw30850step0 raw30850step0Labels := by
      have hz : ∀ j, raw30850 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30850step0 = (fun i j => raw30850 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30850step0 raw30850; decide +kernel
      have hl : raw30850step0Labels = raw30850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30850 raw30850Labels permutation434 hz
    mixedMoment B raw30850step0 raw30850step0Labels = mixedMoment B raw30850step1 raw30850step1Labels := by
      have ha : raw30850step1 = (fun i j => raw30850step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30850step1 raw30850step0; decide +kernel
      have hl : raw30850step1Labels = raw30850step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30850step0 raw30850step0Labels permutation92 permutation4
    mixedMoment B raw30850step1 raw30850step1Labels = mixedMoment B raw30850step2 raw30850step2Labels := by
      have ha : raw30850step2 = -raw30850step1 := by apply Matrix.ext; change ∀ i j, raw30850step2 i j = -(raw30850step1 i j); unfold raw30850step2 raw30850step1; decide +kernel
      have hl : raw30850step2Labels = raw30850step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2679 node2679Labels := by rfl

def raw30851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30851 raw30851Labels = mixedMoment B node3712 node3712Labels := by
  calc
    mixedMoment B raw30851 raw30851Labels = mixedMoment B raw30851step0 raw30851step0Labels := by
      have ha : raw30851step0 = (fun i j => raw30851 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30851step0 raw30851; decide +kernel
      have hl : raw30851step0Labels = raw30851Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30851 raw30851Labels permutation584 permutation2
    mixedMoment B raw30851step0 raw30851step0Labels = mixedMoment B raw30851step1 raw30851step1Labels := by
      have ha : raw30851step1 = -raw30851step0 := by apply Matrix.ext; change ∀ i j, raw30851step1 i j = -(raw30851step0 i j); unfold raw30851step1 raw30851step0; decide +kernel
      have hl : raw30851step1Labels = raw30851step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3712 node3712Labels := by rfl

def raw30852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30852 raw30852Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw30852 raw30852Labels = mixedMoment B raw30852step0 raw30852step0Labels := by
      have hz : ∀ j, raw30852 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30852step0 = (fun i j => raw30852 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30852step0 raw30852; decide +kernel
      have hl : raw30852step0Labels = raw30852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30852 raw30852Labels permutation434 hz
    _ = mixedMoment B node3772 node3772Labels := by rfl

def raw30853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![2, 0, -2], ![1, -1, 0]]
def raw30853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30853 raw30853Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw30853 raw30853Labels = mixedMoment B raw30853step0 raw30853step0Labels := by
      have hz : ∀ j, raw30853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30853step0 = (fun i j => raw30853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30853step0 raw30853; decide +kernel
      have hl : raw30853step0Labels = raw30853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30853 raw30853Labels permutation434 hz
    mixedMoment B raw30853step0 raw30853step0Labels = mixedMoment B raw30853step1 raw30853step1Labels := by
      have ha : raw30853step1 = (fun i j => raw30853step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30853step1 raw30853step0; decide +kernel
      have hl : raw30853step1Labels = raw30853step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30853step0 raw30853step0Labels permutation33 permutation2
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw30854 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![0, 0], ![2, -2], ![0, 0]]
def raw30854Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30854step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![0, 0], ![2, -2]]
def raw30854step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30854step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw30854step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30854 raw30854Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw30854 raw30854Labels = mixedMoment B raw30854step0 raw30854step0Labels := by
      have hz : ∀ j, raw30854 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw30854step0 = (fun i j => raw30854 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw30854step0 raw30854; decide +kernel
      have hl : raw30854step0Labels = raw30854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30854 raw30854Labels permutation590 hz
    mixedMoment B raw30854step0 raw30854step0Labels = mixedMoment B raw30854step1 raw30854step1Labels := by
      have hz : ∀ j, raw30854step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw30854step1 = (fun i j => raw30854step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw30854step1 raw30854step0; decide +kernel
      have hl : raw30854step1Labels = raw30854step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30854step0 raw30854step0Labels permutation104 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

def raw30855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30855 raw30855Labels = mixedMoment B node2395 node2395Labels := by
  calc
    mixedMoment B raw30855 raw30855Labels = mixedMoment B raw30855step0 raw30855step0Labels := by
      have hz : ∀ j, raw30855 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30855step0 = (fun i j => raw30855 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30855step0 raw30855; decide +kernel
      have hl : raw30855step0Labels = raw30855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30855 raw30855Labels permutation434 hz
    _ = mixedMoment B node2395 node2395Labels := by rfl

def raw30856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30856 raw30856Labels = mixedMoment B node3661 node3661Labels := by
  calc
    mixedMoment B raw30856 raw30856Labels = mixedMoment B raw30856step0 raw30856step0Labels := by
      have hz : ∀ j, raw30856 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30856step0 = (fun i j => raw30856 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30856step0 raw30856; decide +kernel
      have hl : raw30856step0Labels = raw30856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30856 raw30856Labels permutation434 hz
    _ = mixedMoment B node3661 node3661Labels := by rfl

def raw30857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 3, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw30857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw30857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30857 raw30857Labels = mixedMoment B node2772 node2772Labels := by
  calc
    mixedMoment B raw30857 raw30857Labels = mixedMoment B raw30857step0 raw30857step0Labels := by
      have hz : ∀ j, raw30857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30857step0 = (fun i j => raw30857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30857step0 raw30857; decide +kernel
      have hl : raw30857step0Labels = raw30857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30857 raw30857Labels permutation434 hz
    mixedMoment B raw30857step0 raw30857step0Labels = mixedMoment B raw30857step1 raw30857step1Labels := by
      have ha : raw30857step1 = (fun i j => raw30857step0 (permutation83 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30857step1 raw30857step0; decide +kernel
      have hl : raw30857step1Labels = raw30857step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30857step0 raw30857step0Labels permutation83 permutation4
    mixedMoment B raw30857step1 raw30857step1Labels = mixedMoment B raw30857step2 raw30857step2Labels := by
      have ha : raw30857step2 = -raw30857step1 := by apply Matrix.ext; change ∀ i j, raw30857step2 i j = -(raw30857step1 i j); unfold raw30857step2 raw30857step1; decide +kernel
      have hl : raw30857step2Labels = raw30857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2772 node2772Labels := by rfl

def raw30858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30858 raw30858Labels = mixedMoment B node3743 node3743Labels := by
  calc
    mixedMoment B raw30858 raw30858Labels = mixedMoment B raw30858step0 raw30858step0Labels := by
      have ha : raw30858step0 = (fun i j => raw30858 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30858step0 raw30858; decide +kernel
      have hl : raw30858step0Labels = raw30858Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30858 raw30858Labels permutation158 permutation2
    _ = mixedMoment B node3743 node3743Labels := by rfl

def raw30859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30859 raw30859Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw30859 raw30859Labels = mixedMoment B raw30859step0 raw30859step0Labels := by
      have hz : ∀ j, raw30859 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30859step0 = (fun i j => raw30859 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30859step0 raw30859; decide +kernel
      have hl : raw30859step0Labels = raw30859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30859 raw30859Labels permutation434 hz
    _ = mixedMoment B node3771 node3771Labels := by rfl

def raw30860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![1, 0, -1]]
def raw30860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30860 raw30860Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw30860 raw30860Labels = mixedMoment B raw30860step0 raw30860step0Labels := by
      have hz : ∀ j, raw30860 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30860step0 = (fun i j => raw30860 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30860step0 raw30860; decide +kernel
      have hl : raw30860step0Labels = raw30860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30860 raw30860Labels permutation434 hz
    mixedMoment B raw30860step0 raw30860step0Labels = mixedMoment B raw30860step1 raw30860step1Labels := by
      have ha : raw30860step1 = (fun i j => raw30860step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30860step1 raw30860step0; decide +kernel
      have hl : raw30860step1Labels = raw30860step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30860step0 raw30860step0Labels permutation33 permutation2
    _ = mixedMoment B node3771 node3771Labels := by rfl

def raw30861 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![0, 0], ![1, -1], ![1, -1]]
def raw30861Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30861step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw30861step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30861step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30861step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30861 raw30861Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw30861 raw30861Labels = mixedMoment B raw30861step0 raw30861step0Labels := by
      have hz : ∀ j, raw30861 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30861step0 = (fun i j => raw30861 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30861step0 raw30861; decide +kernel
      have hl : raw30861step0Labels = raw30861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30861 raw30861Labels permutation434 hz
    mixedMoment B raw30861step0 raw30861step0Labels = mixedMoment B raw30861step1 raw30861step1Labels := by
      have ha : raw30861step1 = (fun i j => raw30861step0 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30861step1 raw30861step0; decide +kernel
      have hl : raw30861step1Labels = raw30861step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30861step0 raw30861step0Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw30862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30862 raw30862Labels = mixedMoment B node2379 node2379Labels := by
  calc
    mixedMoment B raw30862 raw30862Labels = mixedMoment B raw30862step0 raw30862step0Labels := by
      have ha : raw30862step0 = (fun i j => raw30862 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30862step0 raw30862; decide +kernel
      have hl : raw30862step0Labels = raw30862Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30862 raw30862Labels permutation153 permutation2
    _ = mixedMoment B node2379 node2379Labels := by rfl

def raw30863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30863 raw30863Labels = mixedMoment B node3646 node3646Labels := by
  calc
    mixedMoment B raw30863 raw30863Labels = mixedMoment B raw30863step0 raw30863step0Labels := by
      have ha : raw30863step0 = (fun i j => raw30863 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30863step0 raw30863; decide +kernel
      have hl : raw30863step0Labels = raw30863Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30863 raw30863Labels permutation153 permutation2
    _ = mixedMoment B node3646 node3646Labels := by rfl

def raw30864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30864 raw30864Labels = mixedMoment B node3718 node3718Labels := by
  calc
    mixedMoment B raw30864 raw30864Labels = mixedMoment B raw30864step0 raw30864step0Labels := by
      have ha : raw30864step0 = (fun i j => raw30864 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30864step0 raw30864; decide +kernel
      have hl : raw30864step0Labels = raw30864Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30864 raw30864Labels permutation589 permutation2
    mixedMoment B raw30864step0 raw30864step0Labels = mixedMoment B raw30864step1 raw30864step1Labels := by
      have ha : raw30864step1 = -raw30864step0 := by apply Matrix.ext; change ∀ i j, raw30864step1 i j = -(raw30864step0 i j); unfold raw30864step1 raw30864step0; decide +kernel
      have hl : raw30864step1Labels = raw30864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3718 node3718Labels := by rfl

def raw30865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30865 raw30865Labels = mixedMoment B node3718 node3718Labels := by
  calc
    mixedMoment B raw30865 raw30865Labels = mixedMoment B raw30865step0 raw30865step0Labels := by
      have ha : raw30865step0 = (fun i j => raw30865 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30865step0 raw30865; decide +kernel
      have hl : raw30865step0Labels = raw30865Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30865 raw30865Labels permutation584 permutation2
    mixedMoment B raw30865step0 raw30865step0Labels = mixedMoment B raw30865step1 raw30865step1Labels := by
      have ha : raw30865step1 = -raw30865step0 := by apply Matrix.ext; change ∀ i j, raw30865step1 i j = -(raw30865step0 i j); unfold raw30865step1 raw30865step0; decide +kernel
      have hl : raw30865step1Labels = raw30865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3718 node3718Labels := by rfl

def raw30866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30866 raw30866Labels = mixedMoment B node3759 node3759Labels := by
  calc
    _ = mixedMoment B node3759 node3759Labels := by rfl

def raw30867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30867 raw30867Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw30867 raw30867Labels = mixedMoment B raw30867step0 raw30867step0Labels := by
      have ha : raw30867step0 = (fun i j => raw30867 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30867step0 raw30867; decide +kernel
      have hl : raw30867step0Labels = raw30867Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30867 raw30867Labels permutation153 permutation2
    _ = mixedMoment B node3757 node3757Labels := by rfl

def raw30868 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2], ![0, 0]]
def raw30868Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30868step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30868step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30868 raw30868Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw30868 raw30868Labels = mixedMoment B raw30868step0 raw30868step0Labels := by
      have hz : ∀ j, raw30868 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw30868step0 = (fun i j => raw30868 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw30868step0 raw30868; decide +kernel
      have hl : raw30868step0Labels = raw30868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30868 raw30868Labels permutation590 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw30869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw30869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30869 raw30869Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw30869 raw30869Labels = mixedMoment B raw30869step0 raw30869step0Labels := by
      have hz : ∀ j, raw30869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30869step0 = (fun i j => raw30869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30869step0 raw30869; decide +kernel
      have hl : raw30869step0Labels = raw30869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30869 raw30869Labels permutation434 hz
    mixedMoment B raw30869step0 raw30869step0Labels = mixedMoment B raw30869step1 raw30869step1Labels := by
      have ha : raw30869step1 = (fun i j => raw30869step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30869step1 raw30869step0; decide +kernel
      have hl : raw30869step1Labels = raw30869step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30869step0 raw30869step0Labels permutation33 permutation2
    _ = mixedMoment B node2388 node2388Labels := by rfl

def raw30870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw30870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30870 raw30870Labels = mixedMoment B node3654 node3654Labels := by
  calc
    mixedMoment B raw30870 raw30870Labels = mixedMoment B raw30870step0 raw30870step0Labels := by
      have hz : ∀ j, raw30870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30870step0 = (fun i j => raw30870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30870step0 raw30870; decide +kernel
      have hl : raw30870step0Labels = raw30870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30870 raw30870Labels permutation434 hz
    mixedMoment B raw30870step0 raw30870step0Labels = mixedMoment B raw30870step1 raw30870step1Labels := by
      have ha : raw30870step1 = (fun i j => raw30870step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30870step1 raw30870step0; decide +kernel
      have hl : raw30870step1Labels = raw30870step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30870step0 raw30870step0Labels permutation33 permutation2
    _ = mixedMoment B node3654 node3654Labels := by rfl

def raw30871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw30871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30871 raw30871Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw30871 raw30871Labels = mixedMoment B raw30871step0 raw30871step0Labels := by
      have hz : ∀ j, raw30871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30871step0 = (fun i j => raw30871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30871step0 raw30871; decide +kernel
      have hl : raw30871step0Labels = raw30871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30871 raw30871Labels permutation434 hz
    mixedMoment B raw30871step0 raw30871step0Labels = mixedMoment B raw30871step1 raw30871step1Labels := by
      have ha : raw30871step1 = (fun i j => raw30871step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30871step1 raw30871step0; decide +kernel
      have hl : raw30871step1Labels = raw30871step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30871step0 raw30871step0Labels permutation127 permutation2
    mixedMoment B raw30871step1 raw30871step1Labels = mixedMoment B raw30871step2 raw30871step2Labels := by
      have ha : raw30871step2 = -raw30871step1 := by apply Matrix.ext; change ∀ i j, raw30871step2 i j = -(raw30871step1 i j); unfold raw30871step2 raw30871step1; decide +kernel
      have hl : raw30871step2Labels = raw30871step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3702 node3702Labels := by rfl

def raw30872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30872 raw30872Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw30872 raw30872Labels = mixedMoment B raw30872step0 raw30872step0Labels := by
      have ha : raw30872step0 = (fun i j => raw30872 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30872step0 raw30872; decide +kernel
      have hl : raw30872step0Labels = raw30872Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30872 raw30872Labels permutation584 permutation2
    mixedMoment B raw30872step0 raw30872step0Labels = mixedMoment B raw30872step1 raw30872step1Labels := by
      have ha : raw30872step1 = -raw30872step0 := by apply Matrix.ext; change ∀ i j, raw30872step1 i j = -(raw30872step0 i j); unfold raw30872step1 raw30872step0; decide +kernel
      have hl : raw30872step1Labels = raw30872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3681 node3681Labels := by rfl

def raw30873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30873 raw30873Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw30873 raw30873Labels = mixedMoment B raw30873step0 raw30873step0Labels := by
      have hz : ∀ j, raw30873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30873step0 = (fun i j => raw30873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30873step0 raw30873; decide +kernel
      have hl : raw30873step0Labels = raw30873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30873 raw30873Labels permutation434 hz
    _ = mixedMoment B node3767 node3767Labels := by rfl

def raw30874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw30874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30874 raw30874Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw30874 raw30874Labels = mixedMoment B raw30874step0 raw30874step0Labels := by
      have hz : ∀ j, raw30874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30874step0 = (fun i j => raw30874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30874step0 raw30874; decide +kernel
      have hl : raw30874step0Labels = raw30874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30874 raw30874Labels permutation434 hz
    mixedMoment B raw30874step0 raw30874step0Labels = mixedMoment B raw30874step1 raw30874step1Labels := by
      have ha : raw30874step1 = (fun i j => raw30874step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30874step1 raw30874step0; decide +kernel
      have hl : raw30874step1Labels = raw30874step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30874step0 raw30874step0Labels permutation33 permutation2
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw30875 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![0, 0], ![2, -2], ![1, -1]]
def raw30875Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30875step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw30875step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30875step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30875step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30875 raw30875Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw30875 raw30875Labels = mixedMoment B raw30875step0 raw30875step0Labels := by
      have hz : ∀ j, raw30875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30875step0 = (fun i j => raw30875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30875step0 raw30875; decide +kernel
      have hl : raw30875step0Labels = raw30875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30875 raw30875Labels permutation434 hz
    mixedMoment B raw30875step0 raw30875step0Labels = mixedMoment B raw30875step1 raw30875step1Labels := by
      have ha : raw30875step1 = (fun i j => raw30875step0 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30875step1 raw30875step0; decide +kernel
      have hl : raw30875step1Labels = raw30875step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30875step0 raw30875step0Labels permutation33 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw30876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw30876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30876 raw30876Labels = mixedMoment B node2312 node2312Labels := by
  calc
    mixedMoment B raw30876 raw30876Labels = mixedMoment B raw30876step0 raw30876step0Labels := by
      have hz : ∀ j, raw30876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30876step0 = (fun i j => raw30876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30876step0 raw30876; decide +kernel
      have hl : raw30876step0Labels = raw30876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30876 raw30876Labels permutation434 hz
    mixedMoment B raw30876step0 raw30876step0Labels = mixedMoment B raw30876step1 raw30876step1Labels := by
      have ha : raw30876step1 = (fun i j => raw30876step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30876step1 raw30876step0; decide +kernel
      have hl : raw30876step1Labels = raw30876step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30876step0 raw30876step0Labels permutation33 permutation2
    _ = mixedMoment B node2312 node2312Labels := by rfl

def raw30877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30877 raw30877Labels = mixedMoment B node2296 node2296Labels := by
  calc
    mixedMoment B raw30877 raw30877Labels = mixedMoment B raw30877step0 raw30877step0Labels := by
      have ha : raw30877step0 = (fun i j => raw30877 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30877step0 raw30877; decide +kernel
      have hl : raw30877step0Labels = raw30877Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30877 raw30877Labels permutation153 permutation2
    _ = mixedMoment B node2296 node2296Labels := by rfl

def raw30878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw30878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30878 raw30878Labels = mixedMoment B node2300 node2300Labels := by
  calc
    mixedMoment B raw30878 raw30878Labels = mixedMoment B raw30878step0 raw30878step0Labels := by
      have hz : ∀ j, raw30878 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30878step0 = (fun i j => raw30878 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30878step0 raw30878; decide +kernel
      have hl : raw30878step0Labels = raw30878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30878 raw30878Labels permutation434 hz
    mixedMoment B raw30878step0 raw30878step0Labels = mixedMoment B raw30878step1 raw30878step1Labels := by
      have ha : raw30878step1 = (fun i j => raw30878step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30878step1 raw30878step0; decide +kernel
      have hl : raw30878step1Labels = raw30878step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30878step0 raw30878step0Labels permutation33 permutation2
    _ = mixedMoment B node2300 node2300Labels := by rfl

def raw30879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw30879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30879 raw30879Labels = mixedMoment B node2301 node2301Labels := by
  calc
    mixedMoment B raw30879 raw30879Labels = mixedMoment B raw30879step0 raw30879step0Labels := by
      have hz : ∀ j, raw30879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30879step0 = (fun i j => raw30879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30879step0 raw30879; decide +kernel
      have hl : raw30879step0Labels = raw30879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30879 raw30879Labels permutation434 hz
    _ = mixedMoment B node2301 node2301Labels := by rfl

def raw30880 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30880 raw30880Labels = mixedMoment B node3354 node3354Labels := by
  calc
    mixedMoment B raw30880 raw30880Labels = mixedMoment B raw30880step0 raw30880step0Labels := by
      have hz : ∀ j, raw30880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30880step0 = (fun i j => raw30880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30880step0 raw30880; decide +kernel
      have hl : raw30880step0Labels = raw30880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30880 raw30880Labels permutation434 hz
    mixedMoment B raw30880step0 raw30880step0Labels = mixedMoment B raw30880step1 raw30880step1Labels := by
      have ha : raw30880step1 = (fun i j => raw30880step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30880step1 raw30880step0; decide +kernel
      have hl : raw30880step1Labels = raw30880step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30880step0 raw30880step0Labels permutation33 permutation4
    mixedMoment B raw30880step1 raw30880step1Labels = mixedMoment B raw30880step2 raw30880step2Labels := by
      have ha : raw30880step2 = -raw30880step1 := by apply Matrix.ext; change ∀ i j, raw30880step2 i j = -(raw30880step1 i j); unfold raw30880step2 raw30880step1; decide +kernel
      have hl : raw30880step2Labels = raw30880step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3354 node3354Labels := by rfl

def raw30881 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![2, -2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw30881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30881 raw30881Labels = mixedMoment B node1781 node1781Labels := by
  calc
    mixedMoment B raw30881 raw30881Labels = mixedMoment B raw30881step0 raw30881step0Labels := by
      have hz : ∀ j, raw30881 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30881step0 = (fun i j => raw30881 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30881step0 raw30881; decide +kernel
      have hl : raw30881step0Labels = raw30881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30881 raw30881Labels permutation434 hz
    mixedMoment B raw30881step0 raw30881step0Labels = mixedMoment B raw30881step1 raw30881step1Labels := by
      have ha : raw30881step1 = (fun i j => raw30881step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30881step1 raw30881step0; decide +kernel
      have hl : raw30881step1Labels = raw30881step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30881step0 raw30881step0Labels permutation36 permutation4
    mixedMoment B raw30881step1 raw30881step1Labels = mixedMoment B raw30881step2 raw30881step2Labels := by
      have ha : raw30881step2 = -raw30881step1 := by apply Matrix.ext; change ∀ i j, raw30881step2 i j = -(raw30881step1 i j); unfold raw30881step2 raw30881step1; decide +kernel
      have hl : raw30881step2Labels = raw30881step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1781 node1781Labels := by rfl

def raw30882 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30882 raw30882Labels = mixedMoment B node1769 node1769Labels := by
  calc
    mixedMoment B raw30882 raw30882Labels = mixedMoment B raw30882step0 raw30882step0Labels := by
      have ha : raw30882step0 = (fun i j => raw30882 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30882step0 raw30882; decide +kernel
      have hl : raw30882step0Labels = raw30882Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30882 raw30882Labels permutation153 permutation4
    mixedMoment B raw30882step0 raw30882step0Labels = mixedMoment B raw30882step1 raw30882step1Labels := by
      have ha : raw30882step1 = -raw30882step0 := by apply Matrix.ext; change ∀ i j, raw30882step1 i j = -(raw30882step0 i j); unfold raw30882step1 raw30882step0; decide +kernel
      have hl : raw30882step1Labels = raw30882step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1769 node1769Labels := by rfl

def raw30883 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30883 raw30883Labels = mixedMoment B node1773 node1773Labels := by
  calc
    mixedMoment B raw30883 raw30883Labels = mixedMoment B raw30883step0 raw30883step0Labels := by
      have hz : ∀ j, raw30883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30883step0 = (fun i j => raw30883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30883step0 raw30883; decide +kernel
      have hl : raw30883step0Labels = raw30883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30883 raw30883Labels permutation434 hz
    mixedMoment B raw30883step0 raw30883step0Labels = mixedMoment B raw30883step1 raw30883step1Labels := by
      have ha : raw30883step1 = (fun i j => raw30883step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30883step1 raw30883step0; decide +kernel
      have hl : raw30883step1Labels = raw30883step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30883step0 raw30883step0Labels permutation33 permutation4
    mixedMoment B raw30883step1 raw30883step1Labels = mixedMoment B raw30883step2 raw30883step2Labels := by
      have ha : raw30883step2 = -raw30883step1 := by apply Matrix.ext; change ∀ i j, raw30883step2 i j = -(raw30883step1 i j); unfold raw30883step2 raw30883step1; decide +kernel
      have hl : raw30883step2Labels = raw30883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1773 node1773Labels := by rfl

def raw30884 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30884 raw30884Labels = mixedMoment B node1775 node1775Labels := by
  calc
    mixedMoment B raw30884 raw30884Labels = mixedMoment B raw30884step0 raw30884step0Labels := by
      have hz : ∀ j, raw30884 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30884step0 = (fun i j => raw30884 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30884step0 raw30884; decide +kernel
      have hl : raw30884step0Labels = raw30884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30884 raw30884Labels permutation434 hz
    mixedMoment B raw30884step0 raw30884step0Labels = mixedMoment B raw30884step1 raw30884step1Labels := by
      have ha : raw30884step1 = (fun i j => raw30884step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30884step1 raw30884step0; decide +kernel
      have hl : raw30884step1Labels = raw30884step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30884step0 raw30884step0Labels permutation32 permutation4
    mixedMoment B raw30884step1 raw30884step1Labels = mixedMoment B raw30884step2 raw30884step2Labels := by
      have ha : raw30884step2 = -raw30884step1 := by apply Matrix.ext; change ∀ i j, raw30884step2 i j = -(raw30884step1 i j); unfold raw30884step2 raw30884step1; decide +kernel
      have hl : raw30884step2Labels = raw30884step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1775 node1775Labels := by rfl

def raw30885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 1, -3], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30885step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30885 raw30885Labels = mixedMoment B node2792 node2792Labels := by
  calc
    mixedMoment B raw30885 raw30885Labels = mixedMoment B raw30885step0 raw30885step0Labels := by
      have hz : ∀ j, raw30885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30885step0 = (fun i j => raw30885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30885step0 raw30885; decide +kernel
      have hl : raw30885step0Labels = raw30885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30885 raw30885Labels permutation434 hz
    mixedMoment B raw30885step0 raw30885step0Labels = mixedMoment B raw30885step1 raw30885step1Labels := by
      have ha : raw30885step1 = (fun i j => raw30885step0 (permutation56 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30885step1 raw30885step0; decide +kernel
      have hl : raw30885step1Labels = raw30885step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30885step0 raw30885step0Labels permutation56 permutation4
    mixedMoment B raw30885step1 raw30885step1Labels = mixedMoment B raw30885step2 raw30885step2Labels := by
      have ha : raw30885step2 = -raw30885step1 := by apply Matrix.ext; change ∀ i j, raw30885step2 i j = -(raw30885step1 i j); unfold raw30885step2 raw30885step1; decide +kernel
      have hl : raw30885step2Labels = raw30885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2792 node2792Labels := by rfl

def raw30886 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -2, 2], ![0, -2, 2]]
def raw30886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30886step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30886step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30886step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30886 raw30886Labels = mixedMoment B node3361 node3361Labels := by
  calc
    mixedMoment B raw30886 raw30886Labels = mixedMoment B raw30886step0 raw30886step0Labels := by
      have hz : ∀ j, raw30886 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30886step0 = (fun i j => raw30886 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30886step0 raw30886; decide +kernel
      have hl : raw30886step0Labels = raw30886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30886 raw30886Labels permutation434 hz
    mixedMoment B raw30886step0 raw30886step0Labels = mixedMoment B raw30886step1 raw30886step1Labels := by
      have hz : ∀ j, raw30886step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30886step1 = (fun i j => raw30886step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30886step1 raw30886step0; decide +kernel
      have hl : raw30886step1Labels = raw30886step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30886step0 raw30886step0Labels permutation80 hz
    mixedMoment B raw30886step1 raw30886step1Labels = mixedMoment B raw30886step2 raw30886step2Labels := by
      have ha : raw30886step2 = (fun i j => raw30886step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30886step2 raw30886step1; decide +kernel
      have hl : raw30886step2Labels = raw30886step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30886step1 raw30886step1Labels permutation8 permutation4
    mixedMoment B raw30886step2 raw30886step2Labels = mixedMoment B raw30886step3 raw30886step3Labels := by
      have ha : raw30886step3 = -raw30886step2 := by apply Matrix.ext; change ∀ i j, raw30886step3 i j = -(raw30886step2 i j); unfold raw30886step3 raw30886step2; decide +kernel
      have hl : raw30886step3Labels = raw30886step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3361 node3361Labels := by rfl

def raw30887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30887step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30887 raw30887Labels = mixedMoment B node3354 node3354Labels := by
  calc
    mixedMoment B raw30887 raw30887Labels = mixedMoment B raw30887step0 raw30887step0Labels := by
      have hz : ∀ j, raw30887 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30887step0 = (fun i j => raw30887 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30887step0 raw30887; decide +kernel
      have hl : raw30887step0Labels = raw30887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30887 raw30887Labels permutation434 hz
    mixedMoment B raw30887step0 raw30887step0Labels = mixedMoment B raw30887step1 raw30887step1Labels := by
      have ha : raw30887step1 = (fun i j => raw30887step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30887step1 raw30887step0; decide +kernel
      have hl : raw30887step1Labels = raw30887step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30887step0 raw30887step0Labels permutation32 permutation4
    mixedMoment B raw30887step1 raw30887step1Labels = mixedMoment B raw30887step2 raw30887step2Labels := by
      have ha : raw30887step2 = -raw30887step1 := by apply Matrix.ext; change ∀ i j, raw30887step2 i j = -(raw30887step1 i j); unfold raw30887step2 raw30887step1; decide +kernel
      have hl : raw30887step2Labels = raw30887step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3354 node3354Labels := by rfl

def raw30888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30888step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw30888step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw30888step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw30888step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30888 raw30888Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw30888 raw30888Labels = mixedMoment B raw30888step0 raw30888step0Labels := by
      have hz : ∀ j, raw30888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30888step0 = (fun i j => raw30888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30888step0 raw30888; decide +kernel
      have hl : raw30888step0Labels = raw30888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30888 raw30888Labels permutation434 hz
    mixedMoment B raw30888step0 raw30888step0Labels = mixedMoment B raw30888step1 raw30888step1Labels := by
      have hz : ∀ j, raw30888step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30888step1 = (fun i j => raw30888step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30888step1 raw30888step0; decide +kernel
      have hl : raw30888step1Labels = raw30888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30888step0 raw30888step0Labels permutation80 hz
    mixedMoment B raw30888step1 raw30888step1Labels = mixedMoment B raw30888step2 raw30888step2Labels := by
      have hz : ∀ i, raw30888step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw30888step2 = (fun i j => raw30888step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw30888step2 raw30888step1; decide +kernel
      have hl : raw30888step2Labels = (fun j => raw30888step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw30888step1 raw30888step1Labels permutation4 hz
    mixedMoment B raw30888step2 raw30888step2Labels = mixedMoment B raw30888step3 raw30888step3Labels := by
      have ha : raw30888step3 = raw30888step2 := by apply Matrix.ext; unfold raw30888step3 raw30888step2; decide +kernel
      have hl : raw30888step2Labels = labelEmbedding2 ∘ raw30888step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30888step2 raw30888step2Labels raw30888step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4089 node4089Labels := by rfl

def raw30889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30889step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30889 raw30889Labels = mixedMoment B node5327 node5327Labels := by
  calc
    mixedMoment B raw30889 raw30889Labels = mixedMoment B raw30889step0 raw30889step0Labels := by
      have hz : ∀ j, raw30889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30889step0 = (fun i j => raw30889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30889step0 raw30889; decide +kernel
      have hl : raw30889step0Labels = raw30889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30889 raw30889Labels permutation434 hz
    mixedMoment B raw30889step0 raw30889step0Labels = mixedMoment B raw30889step1 raw30889step1Labels := by
      have ha : raw30889step1 = (fun i j => raw30889step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30889step1 raw30889step0; decide +kernel
      have hl : raw30889step1Labels = raw30889step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30889step0 raw30889step0Labels permutation127 permutation7
    mixedMoment B raw30889step1 raw30889step1Labels = mixedMoment B raw30889step2 raw30889step2Labels := by
      have ha : raw30889step2 = raw30889step1 := by apply Matrix.ext; unfold raw30889step2 raw30889step1; decide +kernel
      have hl : raw30889step1Labels = labelEmbedding10 ∘ raw30889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30889step1 raw30889step1Labels raw30889step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5327 node5327Labels := by rfl

def raw30890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30890step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30890 raw30890Labels = mixedMoment B node5327 node5327Labels := by
  calc
    mixedMoment B raw30890 raw30890Labels = mixedMoment B raw30890step0 raw30890step0Labels := by
      have hz : ∀ j, raw30890 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30890step0 = (fun i j => raw30890 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30890step0 raw30890; decide +kernel
      have hl : raw30890step0Labels = raw30890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30890 raw30890Labels permutation346 hz
    mixedMoment B raw30890step0 raw30890step0Labels = mixedMoment B raw30890step1 raw30890step1Labels := by
      have ha : raw30890step1 = (fun i j => raw30890step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30890step1 raw30890step0; decide +kernel
      have hl : raw30890step1Labels = raw30890step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30890step0 raw30890step0Labels permutation127 permutation7
    mixedMoment B raw30890step1 raw30890step1Labels = mixedMoment B raw30890step2 raw30890step2Labels := by
      have ha : raw30890step2 = raw30890step1 := by apply Matrix.ext; unfold raw30890step2 raw30890step1; decide +kernel
      have hl : raw30890step1Labels = labelEmbedding10 ∘ raw30890step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30890step1 raw30890step1Labels raw30890step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5327 node5327Labels := by rfl

def raw30891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30891step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30891step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30891 raw30891Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw30891 raw30891Labels = mixedMoment B raw30891step0 raw30891step0Labels := by
      have hz : ∀ j, raw30891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30891step0 = (fun i j => raw30891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30891step0 raw30891; decide +kernel
      have hl : raw30891step0Labels = raw30891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30891 raw30891Labels permutation434 hz
    mixedMoment B raw30891step0 raw30891step0Labels = mixedMoment B raw30891step1 raw30891step1Labels := by
      have hz : ∀ j, raw30891step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30891step1 = (fun i j => raw30891step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30891step1 raw30891step0; decide +kernel
      have hl : raw30891step1Labels = raw30891step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30891step0 raw30891step0Labels permutation80 hz
    mixedMoment B raw30891step1 raw30891step1Labels = mixedMoment B raw30891step2 raw30891step2Labels := by
      have ha : raw30891step2 = (fun i j => raw30891step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30891step2 raw30891step1; decide +kernel
      have hl : raw30891step2Labels = raw30891step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30891step1 raw30891step1Labels permutation31 permutation7
    mixedMoment B raw30891step2 raw30891step2Labels = mixedMoment B raw30891step3 raw30891step3Labels := by
      have ha : raw30891step3 = raw30891step2 := by apply Matrix.ext; unfold raw30891step3 raw30891step2; decide +kernel
      have hl : raw30891step2Labels = labelEmbedding10 ∘ raw30891step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30891step2 raw30891step2Labels raw30891step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw30892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![2, 0, -2], ![1, 1, -2]]
def raw30892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30892step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30892step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30892step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30892 raw30892Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw30892 raw30892Labels = mixedMoment B raw30892step0 raw30892step0Labels := by
      have hz : ∀ j, raw30892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30892step0 = (fun i j => raw30892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30892step0 raw30892; decide +kernel
      have hl : raw30892step0Labels = raw30892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30892 raw30892Labels permutation434 hz
    mixedMoment B raw30892step0 raw30892step0Labels = mixedMoment B raw30892step1 raw30892step1Labels := by
      have hz : ∀ j, raw30892step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30892step1 = (fun i j => raw30892step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30892step1 raw30892step0; decide +kernel
      have hl : raw30892step1Labels = raw30892step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30892step0 raw30892step0Labels permutation80 hz
    mixedMoment B raw30892step1 raw30892step1Labels = mixedMoment B raw30892step2 raw30892step2Labels := by
      have ha : raw30892step2 = (fun i j => raw30892step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30892step2 raw30892step1; decide +kernel
      have hl : raw30892step2Labels = raw30892step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30892step1 raw30892step1Labels permutation25 permutation7
    mixedMoment B raw30892step2 raw30892step2Labels = mixedMoment B raw30892step3 raw30892step3Labels := by
      have ha : raw30892step3 = raw30892step2 := by apply Matrix.ext; unfold raw30892step3 raw30892step2; decide +kernel
      have hl : raw30892step2Labels = labelEmbedding10 ∘ raw30892step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30892step2 raw30892step2Labels raw30892step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw30893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30893 raw30893Labels = mixedMoment B node4575 node4575Labels := by
  calc
    mixedMoment B raw30893 raw30893Labels = mixedMoment B raw30893step0 raw30893step0Labels := by
      have hz : ∀ j, raw30893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30893step0 = (fun i j => raw30893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30893step0 raw30893; decide +kernel
      have hl : raw30893step0Labels = raw30893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30893 raw30893Labels permutation434 hz
    mixedMoment B raw30893step0 raw30893step0Labels = mixedMoment B raw30893step1 raw30893step1Labels := by
      have hz : ∀ j, raw30893step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30893step1 = (fun i j => raw30893step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30893step1 raw30893step0; decide +kernel
      have hl : raw30893step1Labels = raw30893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30893step0 raw30893step0Labels permutation80 hz
    _ = mixedMoment B node4575 node4575Labels := by rfl

def raw30894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30894 raw30894Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw30894 raw30894Labels = mixedMoment B raw30894step0 raw30894step0Labels := by
      have hz : ∀ j, raw30894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30894step0 = (fun i j => raw30894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30894step0 raw30894; decide +kernel
      have hl : raw30894step0Labels = raw30894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30894 raw30894Labels permutation434 hz
    mixedMoment B raw30894step0 raw30894step0Labels = mixedMoment B raw30894step1 raw30894step1Labels := by
      have ha : raw30894step1 = (fun i j => raw30894step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30894step1 raw30894step0; decide +kernel
      have hl : raw30894step1Labels = raw30894step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30894step0 raw30894step0Labels permutation38 permutation2
    _ = mixedMoment B node5125 node5125Labels := by rfl

def raw30895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30895 raw30895Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw30895 raw30895Labels = mixedMoment B raw30895step0 raw30895step0Labels := by
      have hz : ∀ j, raw30895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30895step0 = (fun i j => raw30895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30895step0 raw30895; decide +kernel
      have hl : raw30895step0Labels = raw30895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30895 raw30895Labels permutation346 hz
    mixedMoment B raw30895step0 raw30895step0Labels = mixedMoment B raw30895step1 raw30895step1Labels := by
      have ha : raw30895step1 = (fun i j => raw30895step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30895step1 raw30895step0; decide +kernel
      have hl : raw30895step1Labels = raw30895step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30895step0 raw30895step0Labels permutation38 permutation2
    _ = mixedMoment B node5125 node5125Labels := by rfl

def raw30896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30896 raw30896Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw30896 raw30896Labels = mixedMoment B raw30896step0 raw30896step0Labels := by
      have hz : ∀ j, raw30896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30896step0 = (fun i j => raw30896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30896step0 raw30896; decide +kernel
      have hl : raw30896step0Labels = raw30896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30896 raw30896Labels permutation434 hz
    mixedMoment B raw30896step0 raw30896step0Labels = mixedMoment B raw30896step1 raw30896step1Labels := by
      have hz : ∀ j, raw30896step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30896step1 = (fun i j => raw30896step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30896step1 raw30896step0; decide +kernel
      have hl : raw30896step1Labels = raw30896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30896step0 raw30896step0Labels permutation80 hz
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw30897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw30897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30897 raw30897Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw30897 raw30897Labels = mixedMoment B raw30897step0 raw30897step0Labels := by
      have hz : ∀ j, raw30897 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30897step0 = (fun i j => raw30897 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30897step0 raw30897; decide +kernel
      have hl : raw30897step0Labels = raw30897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30897 raw30897Labels permutation434 hz
    mixedMoment B raw30897step0 raw30897step0Labels = mixedMoment B raw30897step1 raw30897step1Labels := by
      have hz : ∀ j, raw30897step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30897step1 = (fun i j => raw30897step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30897step1 raw30897step0; decide +kernel
      have hl : raw30897step1Labels = raw30897step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30897step0 raw30897step0Labels permutation80 hz
    mixedMoment B raw30897step1 raw30897step1Labels = mixedMoment B raw30897step2 raw30897step2Labels := by
      have ha : raw30897step2 = (fun i j => raw30897step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30897step2 raw30897step1; decide +kernel
      have hl : raw30897step2Labels = raw30897step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30897step1 raw30897step1Labels permutation9 permutation2
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw30898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30898 raw30898Labels = mixedMoment B node4515 node4515Labels := by
  calc
    mixedMoment B raw30898 raw30898Labels = mixedMoment B raw30898step0 raw30898step0Labels := by
      have hz : ∀ j, raw30898 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30898step0 = (fun i j => raw30898 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30898step0 raw30898; decide +kernel
      have hl : raw30898step0Labels = raw30898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30898 raw30898Labels permutation434 hz
    _ = mixedMoment B node4515 node4515Labels := by rfl

def raw30899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30899 raw30899Labels = mixedMoment B node4915 node4915Labels := by
  calc
    mixedMoment B raw30899 raw30899Labels = mixedMoment B raw30899step0 raw30899step0Labels := by
      have hz : ∀ j, raw30899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30899step0 = (fun i j => raw30899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30899step0 raw30899; decide +kernel
      have hl : raw30899step0Labels = raw30899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30899 raw30899Labels permutation434 hz
    _ = mixedMoment B node4915 node4915Labels := by rfl

def raw30900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30900 raw30900Labels = mixedMoment B node4985 node4985Labels := by
  calc
    mixedMoment B raw30900 raw30900Labels = mixedMoment B raw30900step0 raw30900step0Labels := by
      have ha : raw30900step0 = (fun i j => raw30900 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30900step0 raw30900; decide +kernel
      have hl : raw30900step0Labels = raw30900Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30900 raw30900Labels permutation158 permutation2
    _ = mixedMoment B node4985 node4985Labels := by rfl

def raw30901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30901 raw30901Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw30901 raw30901Labels = mixedMoment B raw30901step0 raw30901step0Labels := by
      have hz : ∀ j, raw30901 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30901step0 = (fun i j => raw30901 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30901step0 raw30901; decide +kernel
      have hl : raw30901step0Labels = raw30901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30901 raw30901Labels permutation434 hz
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw30902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30902 raw30902Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw30902 raw30902Labels = mixedMoment B raw30902step0 raw30902step0Labels := by
      have hz : ∀ j, raw30902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30902step0 = (fun i j => raw30902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30902step0 raw30902; decide +kernel
      have hl : raw30902step0Labels = raw30902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30902 raw30902Labels permutation434 hz
    mixedMoment B raw30902step0 raw30902step0Labels = mixedMoment B raw30902step1 raw30902step1Labels := by
      have ha : raw30902step1 = (fun i j => raw30902step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30902step1 raw30902step0; decide +kernel
      have hl : raw30902step1Labels = raw30902step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30902step0 raw30902step0Labels permutation33 permutation2
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw30903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30903 raw30903Labels = mixedMoment B node4515 node4515Labels := by
  calc
    mixedMoment B raw30903 raw30903Labels = mixedMoment B raw30903step0 raw30903step0Labels := by
      have hz : ∀ j, raw30903 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30903step0 = (fun i j => raw30903 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30903step0 raw30903; decide +kernel
      have hl : raw30903step0Labels = raw30903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30903 raw30903Labels permutation346 hz
    _ = mixedMoment B node4515 node4515Labels := by rfl

def raw30904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30904 raw30904Labels = mixedMoment B node4915 node4915Labels := by
  calc
    mixedMoment B raw30904 raw30904Labels = mixedMoment B raw30904step0 raw30904step0Labels := by
      have hz : ∀ j, raw30904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30904step0 = (fun i j => raw30904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30904step0 raw30904; decide +kernel
      have hl : raw30904step0Labels = raw30904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30904 raw30904Labels permutation346 hz
    _ = mixedMoment B node4915 node4915Labels := by rfl

def raw30905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30905 raw30905Labels = mixedMoment B node4985 node4985Labels := by
  calc
    _ = mixedMoment B node4985 node4985Labels := by rfl

def raw30906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30906 raw30906Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw30906 raw30906Labels = mixedMoment B raw30906step0 raw30906step0Labels := by
      have hz : ∀ j, raw30906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30906step0 = (fun i j => raw30906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30906step0 raw30906; decide +kernel
      have hl : raw30906step0Labels = raw30906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30906 raw30906Labels permutation346 hz
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw30907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 1, -2]]
def raw30907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30907 raw30907Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw30907 raw30907Labels = mixedMoment B raw30907step0 raw30907step0Labels := by
      have hz : ∀ j, raw30907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30907step0 = (fun i j => raw30907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30907step0 raw30907; decide +kernel
      have hl : raw30907step0Labels = raw30907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30907 raw30907Labels permutation346 hz
    mixedMoment B raw30907step0 raw30907step0Labels = mixedMoment B raw30907step1 raw30907step1Labels := by
      have ha : raw30907step1 = (fun i j => raw30907step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30907step1 raw30907step0; decide +kernel
      have hl : raw30907step1Labels = raw30907step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30907step0 raw30907step0Labels permutation33 permutation2
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw30908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw30908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw30908step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30908 raw30908Labels = mixedMoment B node4520 node4520Labels := by
  calc
    mixedMoment B raw30908 raw30908Labels = mixedMoment B raw30908step0 raw30908step0Labels := by
      have hz : ∀ j, raw30908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30908step0 = (fun i j => raw30908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30908step0 raw30908; decide +kernel
      have hl : raw30908step0Labels = raw30908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30908 raw30908Labels permutation434 hz
    mixedMoment B raw30908step0 raw30908step0Labels = mixedMoment B raw30908step1 raw30908step1Labels := by
      have hz : ∀ j, raw30908step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30908step1 = (fun i j => raw30908step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30908step1 raw30908step0; decide +kernel
      have hl : raw30908step1Labels = raw30908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30908step0 raw30908step0Labels permutation80 hz
    mixedMoment B raw30908step1 raw30908step1Labels = mixedMoment B raw30908step2 raw30908step2Labels := by
      have ha : raw30908step2 = (fun i j => raw30908step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30908step2 raw30908step1; decide +kernel
      have hl : raw30908step2Labels = raw30908step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30908step1 raw30908step1Labels permutation9 permutation2
    _ = mixedMoment B node4520 node4520Labels := by rfl

def raw30909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![3, -1, -2], ![2, 0, -2]]
def raw30909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 0, -2], ![3, -1, -2]]
def raw30909step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30909 raw30909Labels = mixedMoment B node4924 node4924Labels := by
  calc
    mixedMoment B raw30909 raw30909Labels = mixedMoment B raw30909step0 raw30909step0Labels := by
      have hz : ∀ j, raw30909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30909step0 = (fun i j => raw30909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30909step0 raw30909; decide +kernel
      have hl : raw30909step0Labels = raw30909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30909 raw30909Labels permutation434 hz
    mixedMoment B raw30909step0 raw30909step0Labels = mixedMoment B raw30909step1 raw30909step1Labels := by
      have hz : ∀ j, raw30909step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30909step1 = (fun i j => raw30909step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30909step1 raw30909step0; decide +kernel
      have hl : raw30909step1Labels = raw30909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30909step0 raw30909step0Labels permutation80 hz
    mixedMoment B raw30909step1 raw30909step1Labels = mixedMoment B raw30909step2 raw30909step2Labels := by
      have ha : raw30909step2 = (fun i j => raw30909step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30909step2 raw30909step1; decide +kernel
      have hl : raw30909step2Labels = raw30909step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30909step1 raw30909step1Labels permutation9 permutation2
    _ = mixedMoment B node4924 node4924Labels := by rfl

def raw30910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30910step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30910 raw30910Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw30910 raw30910Labels = mixedMoment B raw30910step0 raw30910step0Labels := by
      have hz : ∀ j, raw30910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30910step0 = (fun i j => raw30910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30910step0 raw30910; decide +kernel
      have hl : raw30910step0Labels = raw30910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30910 raw30910Labels permutation434 hz
    mixedMoment B raw30910step0 raw30910step0Labels = mixedMoment B raw30910step1 raw30910step1Labels := by
      have ha : raw30910step1 = (fun i j => raw30910step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30910step1 raw30910step0; decide +kernel
      have hl : raw30910step1Labels = raw30910step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30910step0 raw30910step0Labels permutation127 permutation2
    mixedMoment B raw30910step1 raw30910step1Labels = mixedMoment B raw30910step2 raw30910step2Labels := by
      have ha : raw30910step2 = -raw30910step1 := by apply Matrix.ext; change ∀ i j, raw30910step2 i j = -(raw30910step1 i j); unfold raw30910step2 raw30910step1; decide +kernel
      have hl : raw30910step2Labels = raw30910step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4913 node4913Labels := by rfl

def raw30911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30911step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30911 raw30911Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw30911 raw30911Labels = mixedMoment B raw30911step0 raw30911step0Labels := by
      have hz : ∀ j, raw30911 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30911step0 = (fun i j => raw30911 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30911step0 raw30911; decide +kernel
      have hl : raw30911step0Labels = raw30911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30911 raw30911Labels permutation346 hz
    mixedMoment B raw30911step0 raw30911step0Labels = mixedMoment B raw30911step1 raw30911step1Labels := by
      have ha : raw30911step1 = (fun i j => raw30911step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30911step1 raw30911step0; decide +kernel
      have hl : raw30911step1Labels = raw30911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30911step0 raw30911step0Labels permutation127 permutation2
    mixedMoment B raw30911step1 raw30911step1Labels = mixedMoment B raw30911step2 raw30911step2Labels := by
      have ha : raw30911step2 = -raw30911step1 := by apply Matrix.ext; change ∀ i j, raw30911step2 i j = -(raw30911step1 i j); unfold raw30911step2 raw30911step1; decide +kernel
      have hl : raw30911step2Labels = raw30911step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4913 node4913Labels := by rfl

def raw30912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 1, -2]]
def raw30912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![1, 1, -2]]
def raw30912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![3, -1, -2], ![1, 1, -2]]
def raw30912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw30912step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30912 raw30912Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw30912 raw30912Labels = mixedMoment B raw30912step0 raw30912step0Labels := by
      have hz : ∀ j, raw30912 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30912step0 = (fun i j => raw30912 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30912step0 raw30912; decide +kernel
      have hl : raw30912step0Labels = raw30912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30912 raw30912Labels permutation434 hz
    mixedMoment B raw30912step0 raw30912step0Labels = mixedMoment B raw30912step1 raw30912step1Labels := by
      have hz : ∀ j, raw30912step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30912step1 = (fun i j => raw30912step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30912step1 raw30912step0; decide +kernel
      have hl : raw30912step1Labels = raw30912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30912step0 raw30912step0Labels permutation80 hz
    mixedMoment B raw30912step1 raw30912step1Labels = mixedMoment B raw30912step2 raw30912step2Labels := by
      have ha : raw30912step2 = (fun i j => raw30912step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30912step2 raw30912step1; decide +kernel
      have hl : raw30912step2Labels = raw30912step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30912step1 raw30912step1Labels permutation9 permutation2
    _ = mixedMoment B node5021 node5021Labels := by rfl

def raw30913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw30913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30913 raw30913Labels = mixedMoment B node4520 node4520Labels := by
  calc
    mixedMoment B raw30913 raw30913Labels = mixedMoment B raw30913step0 raw30913step0Labels := by
      have hz : ∀ j, raw30913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30913step0 = (fun i j => raw30913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30913step0 raw30913; decide +kernel
      have hl : raw30913step0Labels = raw30913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30913 raw30913Labels permutation434 hz
    mixedMoment B raw30913step0 raw30913step0Labels = mixedMoment B raw30913step1 raw30913step1Labels := by
      have hz : ∀ j, raw30913step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30913step1 = (fun i j => raw30913step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30913step1 raw30913step0; decide +kernel
      have hl : raw30913step1Labels = raw30913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30913step0 raw30913step0Labels permutation80 hz
    _ = mixedMoment B node4520 node4520Labels := by rfl

def raw30914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 0, -2], ![3, -1, -2]]
def raw30914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30914 raw30914Labels = mixedMoment B node4924 node4924Labels := by
  calc
    mixedMoment B raw30914 raw30914Labels = mixedMoment B raw30914step0 raw30914step0Labels := by
      have hz : ∀ j, raw30914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30914step0 = (fun i j => raw30914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30914step0 raw30914; decide +kernel
      have hl : raw30914step0Labels = raw30914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30914 raw30914Labels permutation434 hz
    mixedMoment B raw30914step0 raw30914step0Labels = mixedMoment B raw30914step1 raw30914step1Labels := by
      have hz : ∀ j, raw30914step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30914step1 = (fun i j => raw30914step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30914step1 raw30914step0; decide +kernel
      have hl : raw30914step1Labels = raw30914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30914step0 raw30914step0Labels permutation80 hz
    _ = mixedMoment B node4924 node4924Labels := by rfl

def raw30915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30915 raw30915Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw30915 raw30915Labels = mixedMoment B raw30915step0 raw30915step0Labels := by
      have hz : ∀ j, raw30915 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30915step0 = (fun i j => raw30915 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30915step0 raw30915; decide +kernel
      have hl : raw30915step0Labels = raw30915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30915 raw30915Labels permutation434 hz
    mixedMoment B raw30915step0 raw30915step0Labels = mixedMoment B raw30915step1 raw30915step1Labels := by
      have ha : raw30915step1 = (fun i j => raw30915step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30915step1 raw30915step0; decide +kernel
      have hl : raw30915step1Labels = raw30915step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30915step0 raw30915step0Labels permutation151 permutation2
    mixedMoment B raw30915step1 raw30915step1Labels = mixedMoment B raw30915step2 raw30915step2Labels := by
      have ha : raw30915step2 = -raw30915step1 := by apply Matrix.ext; change ∀ i j, raw30915step2 i j = -(raw30915step1 i j); unfold raw30915step2 raw30915step1; decide +kernel
      have hl : raw30915step2Labels = raw30915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4913 node4913Labels := by rfl

def raw30916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30916step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30916step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30916 raw30916Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw30916 raw30916Labels = mixedMoment B raw30916step0 raw30916step0Labels := by
      have hz : ∀ j, raw30916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30916step0 = (fun i j => raw30916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30916step0 raw30916; decide +kernel
      have hl : raw30916step0Labels = raw30916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30916 raw30916Labels permutation346 hz
    mixedMoment B raw30916step0 raw30916step0Labels = mixedMoment B raw30916step1 raw30916step1Labels := by
      have ha : raw30916step1 = (fun i j => raw30916step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30916step1 raw30916step0; decide +kernel
      have hl : raw30916step1Labels = raw30916step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30916step0 raw30916step0Labels permutation151 permutation2
    mixedMoment B raw30916step1 raw30916step1Labels = mixedMoment B raw30916step2 raw30916step2Labels := by
      have ha : raw30916step2 = -raw30916step1 := by apply Matrix.ext; change ∀ i j, raw30916step2 i j = -(raw30916step1 i j); unfold raw30916step2 raw30916step1; decide +kernel
      have hl : raw30916step2Labels = raw30916step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4913 node4913Labels := by rfl

def raw30917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30917step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw30917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30917 raw30917Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw30917 raw30917Labels = mixedMoment B raw30917step0 raw30917step0Labels := by
      have hz : ∀ j, raw30917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30917step0 = (fun i j => raw30917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30917step0 raw30917; decide +kernel
      have hl : raw30917step0Labels = raw30917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30917 raw30917Labels permutation434 hz
    mixedMoment B raw30917step0 raw30917step0Labels = mixedMoment B raw30917step1 raw30917step1Labels := by
      have hz : ∀ j, raw30917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30917step1 = (fun i j => raw30917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30917step1 raw30917step0; decide +kernel
      have hl : raw30917step1Labels = raw30917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30917step0 raw30917step0Labels permutation80 hz
    _ = mixedMoment B node5021 node5021Labels := by rfl

def raw30918 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, -2, 2], ![0, -2, 2]]
def raw30918step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![-2, 2, 0], ![-2, 2, 0]]
def raw30918step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30918step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw30918step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30918step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw30918step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30918 raw30918Labels = mixedMoment B node5214 node5214Labels := by
  calc
    mixedMoment B raw30918 raw30918Labels = mixedMoment B raw30918step0 raw30918step0Labels := by
      have hz : ∀ j, raw30918 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30918step0 = (fun i j => raw30918 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30918step0 raw30918; decide +kernel
      have hl : raw30918step0Labels = raw30918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30918 raw30918Labels permutation434 hz
    mixedMoment B raw30918step0 raw30918step0Labels = mixedMoment B raw30918step1 raw30918step1Labels := by
      have hz : ∀ j, raw30918step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30918step1 = (fun i j => raw30918step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30918step1 raw30918step0; decide +kernel
      have hl : raw30918step1Labels = raw30918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30918step0 raw30918step0Labels permutation80 hz
    mixedMoment B raw30918step1 raw30918step1Labels = mixedMoment B raw30918step2 raw30918step2Labels := by
      have ha : raw30918step2 = (fun i j => raw30918step1 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30918step2 raw30918step1; decide +kernel
      have hl : raw30918step2Labels = raw30918step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30918step1 raw30918step1Labels permutation14 permutation5
    mixedMoment B raw30918step2 raw30918step2Labels = mixedMoment B raw30918step3 raw30918step3Labels := by
      have ha : raw30918step3 = -raw30918step2 := by apply Matrix.ext; change ∀ i j, raw30918step3 i j = -(raw30918step2 i j); unfold raw30918step3 raw30918step2; decide +kernel
      have hl : raw30918step3Labels = raw30918step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30918step3 raw30918step3Labels = mixedMoment B raw30918step4 raw30918step4Labels := by
      have ha : raw30918step4 = raw30918step3 := by apply Matrix.ext; unfold raw30918step4 raw30918step3; decide +kernel
      have hl : raw30918step3Labels = labelEmbedding8 ∘ raw30918step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30918step3 raw30918step3Labels raw30918step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5214 node5214Labels := by rfl

def raw30919 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw30919step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw30919step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30919 raw30919Labels = mixedMoment B node5193 node5193Labels := by
  calc
    mixedMoment B raw30919 raw30919Labels = mixedMoment B raw30919step0 raw30919step0Labels := by
      have hz : ∀ j, raw30919 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30919step0 = (fun i j => raw30919 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30919step0 raw30919; decide +kernel
      have hl : raw30919step0Labels = raw30919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30919 raw30919Labels permutation434 hz
    mixedMoment B raw30919step0 raw30919step0Labels = mixedMoment B raw30919step1 raw30919step1Labels := by
      have ha : raw30919step1 = (fun i j => raw30919step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30919step1 raw30919step0; decide +kernel
      have hl : raw30919step1Labels = raw30919step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30919step0 raw30919step0Labels permutation32 permutation7
    mixedMoment B raw30919step1 raw30919step1Labels = mixedMoment B raw30919step2 raw30919step2Labels := by
      have ha : raw30919step2 = raw30919step1 := by apply Matrix.ext; unfold raw30919step2 raw30919step1; decide +kernel
      have hl : raw30919step1Labels = labelEmbedding10 ∘ raw30919step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30919step1 raw30919step1Labels raw30919step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5193 node5193Labels := by rfl

def raw30920 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw30920step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30920step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30920step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30920step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30920 raw30920Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw30920 raw30920Labels = mixedMoment B raw30920step0 raw30920step0Labels := by
      have hz : ∀ j, raw30920 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30920step0 = (fun i j => raw30920 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30920step0 raw30920; decide +kernel
      have hl : raw30920step0Labels = raw30920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30920 raw30920Labels permutation434 hz
    mixedMoment B raw30920step0 raw30920step0Labels = mixedMoment B raw30920step1 raw30920step1Labels := by
      have hz : ∀ j, raw30920step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30920step1 = (fun i j => raw30920step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30920step1 raw30920step0; decide +kernel
      have hl : raw30920step1Labels = raw30920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30920step0 raw30920step0Labels permutation80 hz
    mixedMoment B raw30920step1 raw30920step1Labels = mixedMoment B raw30920step2 raw30920step2Labels := by
      have ha : raw30920step2 = (fun i j => raw30920step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30920step2 raw30920step1; decide +kernel
      have hl : raw30920step2Labels = raw30920step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30920step1 raw30920step1Labels permutation9 permutation7
    mixedMoment B raw30920step2 raw30920step2Labels = mixedMoment B raw30920step3 raw30920step3Labels := by
      have ha : raw30920step3 = raw30920step2 := by apply Matrix.ext; unfold raw30920step3 raw30920step2; decide +kernel
      have hl : raw30920step2Labels = labelEmbedding10 ∘ raw30920step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30920step2 raw30920step2Labels raw30920step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw30921 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw30921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30921step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30921 raw30921Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw30921 raw30921Labels = mixedMoment B raw30921step0 raw30921step0Labels := by
      have hz : ∀ j, raw30921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30921step0 = (fun i j => raw30921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30921step0 raw30921; decide +kernel
      have hl : raw30921step0Labels = raw30921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30921 raw30921Labels permutation434 hz
    mixedMoment B raw30921step0 raw30921step0Labels = mixedMoment B raw30921step1 raw30921step1Labels := by
      have hz : ∀ j, raw30921step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30921step1 = (fun i j => raw30921step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30921step1 raw30921step0; decide +kernel
      have hl : raw30921step1Labels = raw30921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30921step0 raw30921step0Labels permutation80 hz
    mixedMoment B raw30921step1 raw30921step1Labels = mixedMoment B raw30921step2 raw30921step2Labels := by
      have ha : raw30921step2 = (fun i j => raw30921step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30921step2 raw30921step1; decide +kernel
      have hl : raw30921step2Labels = raw30921step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30921step1 raw30921step1Labels permutation8 permutation7
    mixedMoment B raw30921step2 raw30921step2Labels = mixedMoment B raw30921step3 raw30921step3Labels := by
      have ha : raw30921step3 = raw30921step2 := by apply Matrix.ext; unfold raw30921step3 raw30921step2; decide +kernel
      have hl : raw30921step2Labels = labelEmbedding10 ∘ raw30921step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30921step2 raw30921step2Labels raw30921step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw30922 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30922step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30922step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30922step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30922step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30922 raw30922Labels = mixedMoment B node4646 node4646Labels := by
  calc
    mixedMoment B raw30922 raw30922Labels = mixedMoment B raw30922step0 raw30922step0Labels := by
      have hz : ∀ j, raw30922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30922step0 = (fun i j => raw30922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30922step0 raw30922; decide +kernel
      have hl : raw30922step0Labels = raw30922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30922 raw30922Labels permutation434 hz
    mixedMoment B raw30922step0 raw30922step0Labels = mixedMoment B raw30922step1 raw30922step1Labels := by
      have ha : raw30922step1 = (fun i j => raw30922step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30922step1 raw30922step0; decide +kernel
      have hl : raw30922step1Labels = raw30922step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30922step0 raw30922step0Labels permutation32 permutation4
    mixedMoment B raw30922step1 raw30922step1Labels = mixedMoment B raw30922step2 raw30922step2Labels := by
      have ha : raw30922step2 = -raw30922step1 := by apply Matrix.ext; change ∀ i j, raw30922step2 i j = -(raw30922step1 i j); unfold raw30922step2 raw30922step1; decide +kernel
      have hl : raw30922step2Labels = raw30922step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30922step2 raw30922step2Labels = mixedMoment B raw30922step3 raw30922step3Labels := by
      have ha : raw30922step3 = raw30922step2 := by apply Matrix.ext; unfold raw30922step3 raw30922step2; decide +kernel
      have hl : raw30922step2Labels = labelEmbedding7 ∘ raw30922step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30922step2 raw30922step2Labels raw30922step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4646 node4646Labels := by rfl

def raw30923 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 2, 0]]
def raw30923step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw30923step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30923step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw30923step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30923 raw30923Labels = mixedMoment B node4984 node4984Labels := by
  calc
    mixedMoment B raw30923 raw30923Labels = mixedMoment B raw30923step0 raw30923step0Labels := by
      have hz : ∀ j, raw30923 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30923step0 = (fun i j => raw30923 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30923step0 raw30923; decide +kernel
      have hl : raw30923step0Labels = raw30923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30923 raw30923Labels permutation434 hz
    mixedMoment B raw30923step0 raw30923step0Labels = mixedMoment B raw30923step1 raw30923step1Labels := by
      have ha : raw30923step1 = (fun i j => raw30923step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30923step1 raw30923step0; decide +kernel
      have hl : raw30923step1Labels = raw30923step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30923step0 raw30923step0Labels permutation56 permutation5
    mixedMoment B raw30923step1 raw30923step1Labels = mixedMoment B raw30923step2 raw30923step2Labels := by
      have ha : raw30923step2 = -raw30923step1 := by apply Matrix.ext; change ∀ i j, raw30923step2 i j = -(raw30923step1 i j); unfold raw30923step2 raw30923step1; decide +kernel
      have hl : raw30923step2Labels = raw30923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30923step2 raw30923step2Labels = mixedMoment B raw30923step3 raw30923step3Labels := by
      have ha : raw30923step3 = raw30923step2 := by apply Matrix.ext; unfold raw30923step3 raw30923step2; decide +kernel
      have hl : raw30923step2Labels = labelEmbedding8 ∘ raw30923step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30923step2 raw30923step2Labels raw30923step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4984 node4984Labels := by rfl

def raw30924 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30924step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30924step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30924step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30924step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30924 raw30924Labels = mixedMoment B node4646 node4646Labels := by
  calc
    mixedMoment B raw30924 raw30924Labels = mixedMoment B raw30924step0 raw30924step0Labels := by
      have hz : ∀ j, raw30924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30924step0 = (fun i j => raw30924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30924step0 raw30924; decide +kernel
      have hl : raw30924step0Labels = raw30924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30924 raw30924Labels permutation346 hz
    mixedMoment B raw30924step0 raw30924step0Labels = mixedMoment B raw30924step1 raw30924step1Labels := by
      have ha : raw30924step1 = (fun i j => raw30924step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30924step1 raw30924step0; decide +kernel
      have hl : raw30924step1Labels = raw30924step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30924step0 raw30924step0Labels permutation32 permutation4
    mixedMoment B raw30924step1 raw30924step1Labels = mixedMoment B raw30924step2 raw30924step2Labels := by
      have ha : raw30924step2 = -raw30924step1 := by apply Matrix.ext; change ∀ i j, raw30924step2 i j = -(raw30924step1 i j); unfold raw30924step2 raw30924step1; decide +kernel
      have hl : raw30924step2Labels = raw30924step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30924step2 raw30924step2Labels = mixedMoment B raw30924step3 raw30924step3Labels := by
      have ha : raw30924step3 = raw30924step2 := by apply Matrix.ext; unfold raw30924step3 raw30924step2; decide +kernel
      have hl : raw30924step2Labels = labelEmbedding7 ∘ raw30924step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30924step2 raw30924step2Labels raw30924step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4646 node4646Labels := by rfl

def raw30925 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 2, 0]]
def raw30925step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw30925step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30925step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw30925step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30925 raw30925Labels = mixedMoment B node4984 node4984Labels := by
  calc
    mixedMoment B raw30925 raw30925Labels = mixedMoment B raw30925step0 raw30925step0Labels := by
      have hz : ∀ j, raw30925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30925step0 = (fun i j => raw30925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30925step0 raw30925; decide +kernel
      have hl : raw30925step0Labels = raw30925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30925 raw30925Labels permutation346 hz
    mixedMoment B raw30925step0 raw30925step0Labels = mixedMoment B raw30925step1 raw30925step1Labels := by
      have ha : raw30925step1 = (fun i j => raw30925step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30925step1 raw30925step0; decide +kernel
      have hl : raw30925step1Labels = raw30925step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30925step0 raw30925step0Labels permutation56 permutation5
    mixedMoment B raw30925step1 raw30925step1Labels = mixedMoment B raw30925step2 raw30925step2Labels := by
      have ha : raw30925step2 = -raw30925step1 := by apply Matrix.ext; change ∀ i j, raw30925step2 i j = -(raw30925step1 i j); unfold raw30925step2 raw30925step1; decide +kernel
      have hl : raw30925step2Labels = raw30925step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30925step2 raw30925step2Labels = mixedMoment B raw30925step3 raw30925step3Labels := by
      have ha : raw30925step3 = raw30925step2 := by apply Matrix.ext; unfold raw30925step3 raw30925step2; decide +kernel
      have hl : raw30925step2Labels = labelEmbedding8 ∘ raw30925step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30925step2 raw30925step2Labels raw30925step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4984 node4984Labels := by rfl

def raw30926 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30926step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30926 raw30926Labels = mixedMoment B node4988 node4988Labels := by
  calc
    mixedMoment B raw30926 raw30926Labels = mixedMoment B raw30926step0 raw30926step0Labels := by
      have ha : raw30926step0 = (fun i j => raw30926 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30926step0 raw30926; decide +kernel
      have hl : raw30926step0Labels = raw30926Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30926 raw30926Labels permutation152 permutation6
    mixedMoment B raw30926step0 raw30926step0Labels = mixedMoment B raw30926step1 raw30926step1Labels := by
      have ha : raw30926step1 = raw30926step0 := by apply Matrix.ext; unfold raw30926step1 raw30926step0; decide +kernel
      have hl : raw30926step0Labels = labelEmbedding9 ∘ raw30926step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30926step0 raw30926step0Labels raw30926step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4988 node4988Labels := by rfl

def raw30927 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30927step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30927 raw30927Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw30927 raw30927Labels = mixedMoment B raw30927step0 raw30927step0Labels := by
      have hz : ∀ j, raw30927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30927step0 = (fun i j => raw30927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30927step0 raw30927; decide +kernel
      have hl : raw30927step0Labels = raw30927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30927 raw30927Labels permutation346 hz
    mixedMoment B raw30927step0 raw30927step0Labels = mixedMoment B raw30927step1 raw30927step1Labels := by
      have ha : raw30927step1 = (fun i j => raw30927step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30927step1 raw30927step0; decide +kernel
      have hl : raw30927step1Labels = raw30927step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30927step0 raw30927step0Labels permutation32 permutation6
    mixedMoment B raw30927step1 raw30927step1Labels = mixedMoment B raw30927step2 raw30927step2Labels := by
      have ha : raw30927step2 = raw30927step1 := by apply Matrix.ext; unfold raw30927step2 raw30927step1; decide +kernel
      have hl : raw30927step1Labels = labelEmbedding9 ∘ raw30927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30927step1 raw30927step1Labels raw30927step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw30928 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30928step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30928step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30928 raw30928Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw30928 raw30928Labels = mixedMoment B raw30928step0 raw30928step0Labels := by
      have hz : ∀ j, raw30928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30928step0 = (fun i j => raw30928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30928step0 raw30928; decide +kernel
      have hl : raw30928step0Labels = raw30928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30928 raw30928Labels permutation346 hz
    mixedMoment B raw30928step0 raw30928step0Labels = mixedMoment B raw30928step1 raw30928step1Labels := by
      have ha : raw30928step1 = (fun i j => raw30928step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30928step1 raw30928step0; decide +kernel
      have hl : raw30928step1Labels = raw30928step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30928step0 raw30928step0Labels permutation33 permutation6
    mixedMoment B raw30928step1 raw30928step1Labels = mixedMoment B raw30928step2 raw30928step2Labels := by
      have ha : raw30928step2 = raw30928step1 := by apply Matrix.ext; unfold raw30928step2 raw30928step1; decide +kernel
      have hl : raw30928step1Labels = labelEmbedding9 ∘ raw30928step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30928step1 raw30928step1Labels raw30928step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw30929 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -3, 2], ![0, -2, 2]]
def raw30929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw30929step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30929step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30929step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30929step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30929step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30929 raw30929Labels = mixedMoment B node4656 node4656Labels := by
  calc
    mixedMoment B raw30929 raw30929Labels = mixedMoment B raw30929step0 raw30929step0Labels := by
      have hz : ∀ j, raw30929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30929step0 = (fun i j => raw30929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30929step0 raw30929; decide +kernel
      have hl : raw30929step0Labels = raw30929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30929 raw30929Labels permutation434 hz
    mixedMoment B raw30929step0 raw30929step0Labels = mixedMoment B raw30929step1 raw30929step1Labels := by
      have hz : ∀ j, raw30929step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30929step1 = (fun i j => raw30929step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30929step1 raw30929step0; decide +kernel
      have hl : raw30929step1Labels = raw30929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30929step0 raw30929step0Labels permutation80 hz
    mixedMoment B raw30929step1 raw30929step1Labels = mixedMoment B raw30929step2 raw30929step2Labels := by
      have ha : raw30929step2 = (fun i j => raw30929step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30929step2 raw30929step1; decide +kernel
      have hl : raw30929step2Labels = raw30929step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30929step1 raw30929step1Labels permutation9 permutation4
    mixedMoment B raw30929step2 raw30929step2Labels = mixedMoment B raw30929step3 raw30929step3Labels := by
      have ha : raw30929step3 = -raw30929step2 := by apply Matrix.ext; change ∀ i j, raw30929step3 i j = -(raw30929step2 i j); unfold raw30929step3 raw30929step2; decide +kernel
      have hl : raw30929step3Labels = raw30929step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30929step3 raw30929step3Labels = mixedMoment B raw30929step4 raw30929step4Labels := by
      have ha : raw30929step4 = raw30929step3 := by apply Matrix.ext; unfold raw30929step4 raw30929step3; decide +kernel
      have hl : raw30929step3Labels = labelEmbedding7 ∘ raw30929step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30929step3 raw30929step3Labels raw30929step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4656 node4656Labels := by rfl

def raw30930 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -3, 2], ![0, -2, 2]]
def raw30930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw30930step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30930step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw30930step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30930 raw30930Labels = mixedMoment B node4925 node4925Labels := by
  calc
    mixedMoment B raw30930 raw30930Labels = mixedMoment B raw30930step0 raw30930step0Labels := by
      have hz : ∀ j, raw30930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30930step0 = (fun i j => raw30930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30930step0 raw30930; decide +kernel
      have hl : raw30930step0Labels = raw30930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30930 raw30930Labels permutation434 hz
    mixedMoment B raw30930step0 raw30930step0Labels = mixedMoment B raw30930step1 raw30930step1Labels := by
      have hz : ∀ j, raw30930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30930step1 = (fun i j => raw30930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30930step1 raw30930step0; decide +kernel
      have hl : raw30930step1Labels = raw30930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30930step0 raw30930step0Labels permutation80 hz
    mixedMoment B raw30930step1 raw30930step1Labels = mixedMoment B raw30930step2 raw30930step2Labels := by
      have ha : raw30930step2 = (fun i j => raw30930step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30930step2 raw30930step1; decide +kernel
      have hl : raw30930step2Labels = raw30930step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30930step1 raw30930step1Labels permutation24 permutation4
    mixedMoment B raw30930step2 raw30930step2Labels = mixedMoment B raw30930step3 raw30930step3Labels := by
      have ha : raw30930step3 = raw30930step2 := by apply Matrix.ext; unfold raw30930step3 raw30930step2; decide +kernel
      have hl : raw30930step2Labels = labelEmbedding7 ∘ raw30930step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30930step2 raw30930step2Labels raw30930step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4925 node4925Labels := by rfl

def raw30931 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw30931step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30931step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw30931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30931 raw30931Labels = mixedMoment B node4914 node4914Labels := by
  calc
    mixedMoment B raw30931 raw30931Labels = mixedMoment B raw30931step0 raw30931step0Labels := by
      have hz : ∀ j, raw30931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30931step0 = (fun i j => raw30931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30931step0 raw30931; decide +kernel
      have hl : raw30931step0Labels = raw30931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30931 raw30931Labels permutation434 hz
    mixedMoment B raw30931step0 raw30931step0Labels = mixedMoment B raw30931step1 raw30931step1Labels := by
      have ha : raw30931step1 = (fun i j => raw30931step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30931step1 raw30931step0; decide +kernel
      have hl : raw30931step1Labels = raw30931step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30931step0 raw30931step0Labels permutation127 permutation4
    mixedMoment B raw30931step1 raw30931step1Labels = mixedMoment B raw30931step2 raw30931step2Labels := by
      have ha : raw30931step2 = raw30931step1 := by apply Matrix.ext; unfold raw30931step2 raw30931step1; decide +kernel
      have hl : raw30931step1Labels = labelEmbedding7 ∘ raw30931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30931step1 raw30931step1Labels raw30931step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4914 node4914Labels := by rfl

def raw30932 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, -2, 2], ![1, -3, 2]]
def raw30932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw30932step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30932step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30932step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30932step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30932step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30932 raw30932Labels = mixedMoment B node4656 node4656Labels := by
  calc
    mixedMoment B raw30932 raw30932Labels = mixedMoment B raw30932step0 raw30932step0Labels := by
      have hz : ∀ j, raw30932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30932step0 = (fun i j => raw30932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30932step0 raw30932; decide +kernel
      have hl : raw30932step0Labels = raw30932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30932 raw30932Labels permutation434 hz
    mixedMoment B raw30932step0 raw30932step0Labels = mixedMoment B raw30932step1 raw30932step1Labels := by
      have hz : ∀ j, raw30932step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30932step1 = (fun i j => raw30932step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30932step1 raw30932step0; decide +kernel
      have hl : raw30932step1Labels = raw30932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30932step0 raw30932step0Labels permutation80 hz
    mixedMoment B raw30932step1 raw30932step1Labels = mixedMoment B raw30932step2 raw30932step2Labels := by
      have ha : raw30932step2 = (fun i j => raw30932step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30932step2 raw30932step1; decide +kernel
      have hl : raw30932step2Labels = raw30932step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30932step1 raw30932step1Labels permutation8 permutation4
    mixedMoment B raw30932step2 raw30932step2Labels = mixedMoment B raw30932step3 raw30932step3Labels := by
      have ha : raw30932step3 = -raw30932step2 := by apply Matrix.ext; change ∀ i j, raw30932step3 i j = -(raw30932step2 i j); unfold raw30932step3 raw30932step2; decide +kernel
      have hl : raw30932step3Labels = raw30932step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30932step3 raw30932step3Labels = mixedMoment B raw30932step4 raw30932step4Labels := by
      have ha : raw30932step4 = raw30932step3 := by apply Matrix.ext; unfold raw30932step4 raw30932step3; decide +kernel
      have hl : raw30932step3Labels = labelEmbedding7 ∘ raw30932step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30932step3 raw30932step3Labels raw30932step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4656 node4656Labels := by rfl

def raw30933 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, -2, 2], ![1, -3, 2]]
def raw30933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw30933step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30933step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw30933step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30933 raw30933Labels = mixedMoment B node4925 node4925Labels := by
  calc
    mixedMoment B raw30933 raw30933Labels = mixedMoment B raw30933step0 raw30933step0Labels := by
      have hz : ∀ j, raw30933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30933step0 = (fun i j => raw30933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30933step0 raw30933; decide +kernel
      have hl : raw30933step0Labels = raw30933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30933 raw30933Labels permutation434 hz
    mixedMoment B raw30933step0 raw30933step0Labels = mixedMoment B raw30933step1 raw30933step1Labels := by
      have hz : ∀ j, raw30933step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30933step1 = (fun i j => raw30933step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30933step1 raw30933step0; decide +kernel
      have hl : raw30933step1Labels = raw30933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30933step0 raw30933step0Labels permutation80 hz
    mixedMoment B raw30933step1 raw30933step1Labels = mixedMoment B raw30933step2 raw30933step2Labels := by
      have ha : raw30933step2 = (fun i j => raw30933step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30933step2 raw30933step1; decide +kernel
      have hl : raw30933step2Labels = raw30933step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30933step1 raw30933step1Labels permutation30 permutation4
    mixedMoment B raw30933step2 raw30933step2Labels = mixedMoment B raw30933step3 raw30933step3Labels := by
      have ha : raw30933step3 = raw30933step2 := by apply Matrix.ext; unfold raw30933step3 raw30933step2; decide +kernel
      have hl : raw30933step2Labels = labelEmbedding7 ∘ raw30933step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30933step2 raw30933step2Labels raw30933step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4925 node4925Labels := by rfl

def raw30934 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw30934step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30934step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw30934step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30934 raw30934Labels = mixedMoment B node4914 node4914Labels := by
  calc
    mixedMoment B raw30934 raw30934Labels = mixedMoment B raw30934step0 raw30934step0Labels := by
      have hz : ∀ j, raw30934 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30934step0 = (fun i j => raw30934 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30934step0 raw30934; decide +kernel
      have hl : raw30934step0Labels = raw30934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30934 raw30934Labels permutation434 hz
    mixedMoment B raw30934step0 raw30934step0Labels = mixedMoment B raw30934step1 raw30934step1Labels := by
      have ha : raw30934step1 = (fun i j => raw30934step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30934step1 raw30934step0; decide +kernel
      have hl : raw30934step1Labels = raw30934step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30934step0 raw30934step0Labels permutation151 permutation4
    mixedMoment B raw30934step1 raw30934step1Labels = mixedMoment B raw30934step2 raw30934step2Labels := by
      have ha : raw30934step2 = raw30934step1 := by apply Matrix.ext; unfold raw30934step2 raw30934step1; decide +kernel
      have hl : raw30934step1Labels = labelEmbedding7 ∘ raw30934step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30934step1 raw30934step1Labels raw30934step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4914 node4914Labels := by rfl

def raw30935 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw30935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw30935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, -1, 2], ![1, -3, 2]]
def raw30935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw30935step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30935step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw30935step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30935 raw30935Labels = mixedMoment B node5023 node5023Labels := by
  calc
    mixedMoment B raw30935 raw30935Labels = mixedMoment B raw30935step0 raw30935step0Labels := by
      have hz : ∀ j, raw30935 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30935step0 = (fun i j => raw30935 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30935step0 raw30935; decide +kernel
      have hl : raw30935step0Labels = raw30935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30935 raw30935Labels permutation434 hz
    mixedMoment B raw30935step0 raw30935step0Labels = mixedMoment B raw30935step1 raw30935step1Labels := by
      have hz : ∀ j, raw30935step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30935step1 = (fun i j => raw30935step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30935step1 raw30935step0; decide +kernel
      have hl : raw30935step1Labels = raw30935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30935step0 raw30935step0Labels permutation80 hz
    mixedMoment B raw30935step1 raw30935step1Labels = mixedMoment B raw30935step2 raw30935step2Labels := by
      have ha : raw30935step2 = (fun i j => raw30935step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30935step2 raw30935step1; decide +kernel
      have hl : raw30935step2Labels = raw30935step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30935step1 raw30935step1Labels permutation31 permutation4
    mixedMoment B raw30935step2 raw30935step2Labels = mixedMoment B raw30935step3 raw30935step3Labels := by
      have ha : raw30935step3 = raw30935step2 := by apply Matrix.ext; unfold raw30935step3 raw30935step2; decide +kernel
      have hl : raw30935step2Labels = labelEmbedding7 ∘ raw30935step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30935step2 raw30935step2Labels raw30935step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5023 node5023Labels := by rfl

def raw30936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw30936step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30936step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30936step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30936step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30936step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30936 raw30936Labels = mixedMoment B node5297 node5297Labels := by
  calc
    mixedMoment B raw30936 raw30936Labels = mixedMoment B raw30936step0 raw30936step0Labels := by
      have hz : ∀ j, raw30936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30936step0 = (fun i j => raw30936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30936step0 raw30936; decide +kernel
      have hl : raw30936step0Labels = raw30936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30936 raw30936Labels permutation434 hz
    mixedMoment B raw30936step0 raw30936step0Labels = mixedMoment B raw30936step1 raw30936step1Labels := by
      have hz : ∀ j, raw30936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30936step1 = (fun i j => raw30936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30936step1 raw30936step0; decide +kernel
      have hl : raw30936step1Labels = raw30936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30936step0 raw30936step0Labels permutation80 hz
    mixedMoment B raw30936step1 raw30936step1Labels = mixedMoment B raw30936step2 raw30936step2Labels := by
      have ha : raw30936step2 = (fun i j => raw30936step1 (permutation16 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30936step2 raw30936step1; decide +kernel
      have hl : raw30936step2Labels = raw30936step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30936step1 raw30936step1Labels permutation16 permutation5
    mixedMoment B raw30936step2 raw30936step2Labels = mixedMoment B raw30936step3 raw30936step3Labels := by
      have ha : raw30936step3 = -raw30936step2 := by apply Matrix.ext; change ∀ i j, raw30936step3 i j = -(raw30936step2 i j); unfold raw30936step3 raw30936step2; decide +kernel
      have hl : raw30936step3Labels = raw30936step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30936step3 raw30936step3Labels = mixedMoment B raw30936step4 raw30936step4Labels := by
      have ha : raw30936step4 = raw30936step3 := by apply Matrix.ext; unfold raw30936step4 raw30936step3; decide +kernel
      have hl : raw30936step3Labels = labelEmbedding8 ∘ raw30936step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30936step3 raw30936step3Labels raw30936step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5297 node5297Labels := by rfl

def raw30937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30937step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30937step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30937step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30937step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30937 raw30937Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw30937 raw30937Labels = mixedMoment B raw30937step0 raw30937step0Labels := by
      have hz : ∀ j, raw30937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30937step0 = (fun i j => raw30937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30937step0 raw30937; decide +kernel
      have hl : raw30937step0Labels = raw30937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30937 raw30937Labels permutation434 hz
    mixedMoment B raw30937step0 raw30937step0Labels = mixedMoment B raw30937step1 raw30937step1Labels := by
      have ha : raw30937step1 = (fun i j => raw30937step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30937step1 raw30937step0; decide +kernel
      have hl : raw30937step1Labels = raw30937step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30937step0 raw30937step0Labels permutation42 permutation7
    mixedMoment B raw30937step1 raw30937step1Labels = mixedMoment B raw30937step2 raw30937step2Labels := by
      have ha : raw30937step2 = -raw30937step1 := by apply Matrix.ext; change ∀ i j, raw30937step2 i j = -(raw30937step1 i j); unfold raw30937step2 raw30937step1; decide +kernel
      have hl : raw30937step2Labels = raw30937step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30937step2 raw30937step2Labels = mixedMoment B raw30937step3 raw30937step3Labels := by
      have ha : raw30937step3 = raw30937step2 := by apply Matrix.ext; unfold raw30937step3 raw30937step2; decide +kernel
      have hl : raw30937step2Labels = labelEmbedding10 ∘ raw30937step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30937step2 raw30937step2Labels raw30937step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw30938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30938step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30938step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30938step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30938step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30938 raw30938Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw30938 raw30938Labels = mixedMoment B raw30938step0 raw30938step0Labels := by
      have hz : ∀ j, raw30938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30938step0 = (fun i j => raw30938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30938step0 raw30938; decide +kernel
      have hl : raw30938step0Labels = raw30938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30938 raw30938Labels permutation346 hz
    mixedMoment B raw30938step0 raw30938step0Labels = mixedMoment B raw30938step1 raw30938step1Labels := by
      have ha : raw30938step1 = (fun i j => raw30938step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30938step1 raw30938step0; decide +kernel
      have hl : raw30938step1Labels = raw30938step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30938step0 raw30938step0Labels permutation42 permutation7
    mixedMoment B raw30938step1 raw30938step1Labels = mixedMoment B raw30938step2 raw30938step2Labels := by
      have ha : raw30938step2 = -raw30938step1 := by apply Matrix.ext; change ∀ i j, raw30938step2 i j = -(raw30938step1 i j); unfold raw30938step2 raw30938step1; decide +kernel
      have hl : raw30938step2Labels = raw30938step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30938step2 raw30938step2Labels = mixedMoment B raw30938step3 raw30938step3Labels := by
      have ha : raw30938step3 = raw30938step2 := by apply Matrix.ext; unfold raw30938step3 raw30938step2; decide +kernel
      have hl : raw30938step2Labels = labelEmbedding10 ∘ raw30938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30938step2 raw30938step2Labels raw30938step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw30939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw30939step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30939step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30939step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30939step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30939 raw30939Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw30939 raw30939Labels = mixedMoment B raw30939step0 raw30939step0Labels := by
      have hz : ∀ j, raw30939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30939step0 = (fun i j => raw30939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30939step0 raw30939; decide +kernel
      have hl : raw30939step0Labels = raw30939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30939 raw30939Labels permutation434 hz
    mixedMoment B raw30939step0 raw30939step0Labels = mixedMoment B raw30939step1 raw30939step1Labels := by
      have hz : ∀ j, raw30939step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30939step1 = (fun i j => raw30939step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30939step1 raw30939step0; decide +kernel
      have hl : raw30939step1Labels = raw30939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30939step0 raw30939step0Labels permutation80 hz
    mixedMoment B raw30939step1 raw30939step1Labels = mixedMoment B raw30939step2 raw30939step2Labels := by
      have ha : raw30939step2 = (fun i j => raw30939step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30939step2 raw30939step1; decide +kernel
      have hl : raw30939step2Labels = raw30939step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30939step1 raw30939step1Labels permutation12 permutation7
    mixedMoment B raw30939step2 raw30939step2Labels = mixedMoment B raw30939step3 raw30939step3Labels := by
      have ha : raw30939step3 = -raw30939step2 := by apply Matrix.ext; change ∀ i j, raw30939step3 i j = -(raw30939step2 i j); unfold raw30939step3 raw30939step2; decide +kernel
      have hl : raw30939step3Labels = raw30939step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30939step3 raw30939step3Labels = mixedMoment B raw30939step4 raw30939step4Labels := by
      have ha : raw30939step4 = raw30939step3 := by apply Matrix.ext; unfold raw30939step4 raw30939step3; decide +kernel
      have hl : raw30939step3Labels = labelEmbedding10 ∘ raw30939step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30939step3 raw30939step3Labels raw30939step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw30940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30940step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw30940step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30940step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30940step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30940step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30940step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30940 raw30940Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw30940 raw30940Labels = mixedMoment B raw30940step0 raw30940step0Labels := by
      have hz : ∀ j, raw30940 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30940step0 = (fun i j => raw30940 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30940step0 raw30940; decide +kernel
      have hl : raw30940step0Labels = raw30940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30940 raw30940Labels permutation434 hz
    mixedMoment B raw30940step0 raw30940step0Labels = mixedMoment B raw30940step1 raw30940step1Labels := by
      have hz : ∀ j, raw30940step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30940step1 = (fun i j => raw30940step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30940step1 raw30940step0; decide +kernel
      have hl : raw30940step1Labels = raw30940step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30940step0 raw30940step0Labels permutation80 hz
    mixedMoment B raw30940step1 raw30940step1Labels = mixedMoment B raw30940step2 raw30940step2Labels := by
      have ha : raw30940step2 = (fun i j => raw30940step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30940step2 raw30940step1; decide +kernel
      have hl : raw30940step2Labels = raw30940step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30940step1 raw30940step1Labels permutation12 permutation7
    mixedMoment B raw30940step2 raw30940step2Labels = mixedMoment B raw30940step3 raw30940step3Labels := by
      have ha : raw30940step3 = -raw30940step2 := by apply Matrix.ext; change ∀ i j, raw30940step3 i j = -(raw30940step2 i j); unfold raw30940step3 raw30940step2; decide +kernel
      have hl : raw30940step3Labels = raw30940step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30940step3 raw30940step3Labels = mixedMoment B raw30940step4 raw30940step4Labels := by
      have ha : raw30940step4 = raw30940step3 := by apply Matrix.ext; unfold raw30940step4 raw30940step3; decide +kernel
      have hl : raw30940step3Labels = labelEmbedding10 ∘ raw30940step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30940step3 raw30940step3Labels raw30940step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw30941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30941step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30941 raw30941Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw30941 raw30941Labels = mixedMoment B raw30941step0 raw30941step0Labels := by
      have hz : ∀ j, raw30941 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30941step0 = (fun i j => raw30941 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30941step0 raw30941; decide +kernel
      have hl : raw30941step0Labels = raw30941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30941 raw30941Labels permutation434 hz
    mixedMoment B raw30941step0 raw30941step0Labels = mixedMoment B raw30941step1 raw30941step1Labels := by
      have hz : ∀ j, raw30941step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30941step1 = (fun i j => raw30941step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30941step1 raw30941step0; decide +kernel
      have hl : raw30941step1Labels = raw30941step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30941step0 raw30941step0Labels permutation80 hz
    mixedMoment B raw30941step1 raw30941step1Labels = mixedMoment B raw30941step2 raw30941step2Labels := by
      have ha : raw30941step2 = (fun i j => raw30941step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30941step2 raw30941step1; decide +kernel
      have hl : raw30941step2Labels = raw30941step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30941step1 raw30941step1Labels permutation9 permutation2
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw30942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30942 raw30942Labels = mixedMoment B node4700 node4700Labels := by
  calc
    mixedMoment B raw30942 raw30942Labels = mixedMoment B raw30942step0 raw30942step0Labels := by
      have hz : ∀ j, raw30942 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30942step0 = (fun i j => raw30942 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30942step0 raw30942; decide +kernel
      have hl : raw30942step0Labels = raw30942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30942 raw30942Labels permutation434 hz
    mixedMoment B raw30942step0 raw30942step0Labels = mixedMoment B raw30942step1 raw30942step1Labels := by
      have ha : raw30942step1 = (fun i j => raw30942step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30942step1 raw30942step0; decide +kernel
      have hl : raw30942step1Labels = raw30942step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30942step0 raw30942step0Labels permutation33 permutation2
    _ = mixedMoment B node4700 node4700Labels := by rfl

def raw30943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30943 raw30943Labels = mixedMoment B node4773 node4773Labels := by
  calc
    mixedMoment B raw30943 raw30943Labels = mixedMoment B raw30943step0 raw30943step0Labels := by
      have ha : raw30943step0 = (fun i j => raw30943 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30943step0 raw30943; decide +kernel
      have hl : raw30943step0Labels = raw30943Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30943 raw30943Labels permutation201 permutation2
    _ = mixedMoment B node4773 node4773Labels := by rfl

def raw30944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30944 raw30944Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw30944 raw30944Labels = mixedMoment B raw30944step0 raw30944step0Labels := by
      have hz : ∀ j, raw30944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30944step0 = (fun i j => raw30944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30944step0 raw30944; decide +kernel
      have hl : raw30944step0Labels = raw30944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30944 raw30944Labels permutation434 hz
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw30945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30945 raw30945Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw30945 raw30945Labels = mixedMoment B raw30945step0 raw30945step0Labels := by
      have hz : ∀ j, raw30945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30945step0 = (fun i j => raw30945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30945step0 raw30945; decide +kernel
      have hl : raw30945step0Labels = raw30945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30945 raw30945Labels permutation434 hz
    mixedMoment B raw30945step0 raw30945step0Labels = mixedMoment B raw30945step1 raw30945step1Labels := by
      have ha : raw30945step1 = (fun i j => raw30945step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30945step1 raw30945step0; decide +kernel
      have hl : raw30945step1Labels = raw30945step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30945step0 raw30945step0Labels permutation33 permutation2
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw30946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30946 raw30946Labels = mixedMoment B node4700 node4700Labels := by
  calc
    mixedMoment B raw30946 raw30946Labels = mixedMoment B raw30946step0 raw30946step0Labels := by
      have hz : ∀ j, raw30946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30946step0 = (fun i j => raw30946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30946step0 raw30946; decide +kernel
      have hl : raw30946step0Labels = raw30946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30946 raw30946Labels permutation346 hz
    mixedMoment B raw30946step0 raw30946step0Labels = mixedMoment B raw30946step1 raw30946step1Labels := by
      have ha : raw30946step1 = (fun i j => raw30946step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30946step1 raw30946step0; decide +kernel
      have hl : raw30946step1Labels = raw30946step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30946step0 raw30946step0Labels permutation33 permutation2
    _ = mixedMoment B node4700 node4700Labels := by rfl

def raw30947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30947 raw30947Labels = mixedMoment B node4773 node4773Labels := by
  calc
    mixedMoment B raw30947 raw30947Labels = mixedMoment B raw30947step0 raw30947step0Labels := by
      have ha : raw30947step0 = (fun i j => raw30947 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30947step0 raw30947; decide +kernel
      have hl : raw30947step0Labels = raw30947Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30947 raw30947Labels permutation177 permutation2
    _ = mixedMoment B node4773 node4773Labels := by rfl

def raw30948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30948 raw30948Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw30948 raw30948Labels = mixedMoment B raw30948step0 raw30948step0Labels := by
      have hz : ∀ j, raw30948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30948step0 = (fun i j => raw30948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30948step0 raw30948; decide +kernel
      have hl : raw30948step0Labels = raw30948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30948 raw30948Labels permutation346 hz
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw30949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30949step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30949 raw30949Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw30949 raw30949Labels = mixedMoment B raw30949step0 raw30949step0Labels := by
      have hz : ∀ j, raw30949 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30949step0 = (fun i j => raw30949 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30949step0 raw30949; decide +kernel
      have hl : raw30949step0Labels = raw30949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30949 raw30949Labels permutation346 hz
    mixedMoment B raw30949step0 raw30949step0Labels = mixedMoment B raw30949step1 raw30949step1Labels := by
      have ha : raw30949step1 = (fun i j => raw30949step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30949step1 raw30949step0; decide +kernel
      have hl : raw30949step1Labels = raw30949step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30949step0 raw30949step0Labels permutation33 permutation2
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw30950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30950step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30950 raw30950Labels = mixedMoment B node4704 node4704Labels := by
  calc
    mixedMoment B raw30950 raw30950Labels = mixedMoment B raw30950step0 raw30950step0Labels := by
      have hz : ∀ j, raw30950 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30950step0 = (fun i j => raw30950 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30950step0 raw30950; decide +kernel
      have hl : raw30950step0Labels = raw30950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30950 raw30950Labels permutation434 hz
    mixedMoment B raw30950step0 raw30950step0Labels = mixedMoment B raw30950step1 raw30950step1Labels := by
      have hz : ∀ j, raw30950step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30950step1 = (fun i j => raw30950step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30950step1 raw30950step0; decide +kernel
      have hl : raw30950step1Labels = raw30950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30950step0 raw30950step0Labels permutation80 hz
    mixedMoment B raw30950step1 raw30950step1Labels = mixedMoment B raw30950step2 raw30950step2Labels := by
      have ha : raw30950step2 = (fun i j => raw30950step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30950step2 raw30950step1; decide +kernel
      have hl : raw30950step2Labels = raw30950step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30950step1 raw30950step1Labels permutation9 permutation2
    _ = mixedMoment B node4704 node4704Labels := by rfl

def raw30951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30951 raw30951Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw30951 raw30951Labels = mixedMoment B raw30951step0 raw30951step0Labels := by
      have hz : ∀ j, raw30951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30951step0 = (fun i j => raw30951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30951step0 raw30951; decide +kernel
      have hl : raw30951step0Labels = raw30951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30951 raw30951Labels permutation434 hz
    mixedMoment B raw30951step0 raw30951step0Labels = mixedMoment B raw30951step1 raw30951step1Labels := by
      have ha : raw30951step1 = (fun i j => raw30951step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30951step1 raw30951step0; decide +kernel
      have hl : raw30951step1Labels = raw30951step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30951step0 raw30951step0Labels permutation39 permutation2
    _ = mixedMoment B node4776 node4776Labels := by rfl

def raw30952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30952 raw30952Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw30952 raw30952Labels = mixedMoment B raw30952step0 raw30952step0Labels := by
      have hz : ∀ j, raw30952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30952step0 = (fun i j => raw30952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30952step0 raw30952; decide +kernel
      have hl : raw30952step0Labels = raw30952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30952 raw30952Labels permutation346 hz
    mixedMoment B raw30952step0 raw30952step0Labels = mixedMoment B raw30952step1 raw30952step1Labels := by
      have ha : raw30952step1 = (fun i j => raw30952step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30952step1 raw30952step0; decide +kernel
      have hl : raw30952step1Labels = raw30952step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30952step0 raw30952step0Labels permutation39 permutation2
    _ = mixedMoment B node4776 node4776Labels := by rfl

def raw30953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![3, -1, -2], ![1, -1, 0]]
def raw30953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30953 raw30953Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw30953 raw30953Labels = mixedMoment B raw30953step0 raw30953step0Labels := by
      have hz : ∀ j, raw30953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30953step0 = (fun i j => raw30953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30953step0 raw30953; decide +kernel
      have hl : raw30953step0Labels = raw30953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30953 raw30953Labels permutation434 hz
    mixedMoment B raw30953step0 raw30953step0Labels = mixedMoment B raw30953step1 raw30953step1Labels := by
      have hz : ∀ j, raw30953step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30953step1 = (fun i j => raw30953step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30953step1 raw30953step0; decide +kernel
      have hl : raw30953step1Labels = raw30953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30953step0 raw30953step0Labels permutation80 hz
    mixedMoment B raw30953step1 raw30953step1Labels = mixedMoment B raw30953step2 raw30953step2Labels := by
      have ha : raw30953step2 = (fun i j => raw30953step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30953step2 raw30953step1; decide +kernel
      have hl : raw30953step2Labels = raw30953step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30953step1 raw30953step1Labels permutation9 permutation2
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw30954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30954step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30954step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, -1, 3], ![-3, 3, 0]]
def raw30954step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30954step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30954step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30954step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30954step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30954 raw30954Labels = mixedMoment B node4694 node4694Labels := by
  calc
    mixedMoment B raw30954 raw30954Labels = mixedMoment B raw30954step0 raw30954step0Labels := by
      have hz : ∀ j, raw30954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30954step0 = (fun i j => raw30954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30954step0 raw30954; decide +kernel
      have hl : raw30954step0Labels = raw30954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30954 raw30954Labels permutation434 hz
    mixedMoment B raw30954step0 raw30954step0Labels = mixedMoment B raw30954step1 raw30954step1Labels := by
      have hz : ∀ j, raw30954step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30954step1 = (fun i j => raw30954step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30954step1 raw30954step0; decide +kernel
      have hl : raw30954step1Labels = raw30954step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30954step0 raw30954step0Labels permutation80 hz
    mixedMoment B raw30954step1 raw30954step1Labels = mixedMoment B raw30954step2 raw30954step2Labels := by
      have ha : raw30954step2 = (fun i j => raw30954step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30954step2 raw30954step1; decide +kernel
      have hl : raw30954step2Labels = raw30954step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30954step1 raw30954step1Labels permutation31 permutation3
    mixedMoment B raw30954step2 raw30954step2Labels = mixedMoment B raw30954step3 raw30954step3Labels := by
      have ha : raw30954step3 = -raw30954step2 := by apply Matrix.ext; change ∀ i j, raw30954step3 i j = -(raw30954step2 i j); unfold raw30954step3 raw30954step2; decide +kernel
      have hl : raw30954step3Labels = raw30954step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30954step3 raw30954step3Labels = mixedMoment B raw30954step4 raw30954step4Labels := by
      have ha : raw30954step4 = raw30954step3 := by apply Matrix.ext; unfold raw30954step4 raw30954step3; decide +kernel
      have hl : raw30954step3Labels = labelEmbedding6 ∘ raw30954step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30954step3 raw30954step3Labels raw30954step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4694 node4694Labels := by rfl

def raw30955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30955step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30955step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30955step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30955step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30955 raw30955Labels = mixedMoment B node4687 node4687Labels := by
  calc
    mixedMoment B raw30955 raw30955Labels = mixedMoment B raw30955step0 raw30955step0Labels := by
      have hz : ∀ j, raw30955 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30955step0 = (fun i j => raw30955 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30955step0 raw30955; decide +kernel
      have hl : raw30955step0Labels = raw30955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30955 raw30955Labels permutation434 hz
    mixedMoment B raw30955step0 raw30955step0Labels = mixedMoment B raw30955step1 raw30955step1Labels := by
      have ha : raw30955step1 = (fun i j => raw30955step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30955step1 raw30955step0; decide +kernel
      have hl : raw30955step1Labels = raw30955step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30955step0 raw30955step0Labels permutation151 permutation3
    mixedMoment B raw30955step1 raw30955step1Labels = mixedMoment B raw30955step2 raw30955step2Labels := by
      have ha : raw30955step2 = -raw30955step1 := by apply Matrix.ext; change ∀ i j, raw30955step2 i j = -(raw30955step1 i j); unfold raw30955step2 raw30955step1; decide +kernel
      have hl : raw30955step2Labels = raw30955step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30955step2 raw30955step2Labels = mixedMoment B raw30955step3 raw30955step3Labels := by
      have ha : raw30955step3 = raw30955step2 := by apply Matrix.ext; unfold raw30955step3 raw30955step2; decide +kernel
      have hl : raw30955step2Labels = labelEmbedding6 ∘ raw30955step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30955step2 raw30955step2Labels raw30955step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4687 node4687Labels := by rfl

def raw30956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30956step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30956step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30956step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30956step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30956 raw30956Labels = mixedMoment B node4687 node4687Labels := by
  calc
    mixedMoment B raw30956 raw30956Labels = mixedMoment B raw30956step0 raw30956step0Labels := by
      have hz : ∀ j, raw30956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30956step0 = (fun i j => raw30956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30956step0 raw30956; decide +kernel
      have hl : raw30956step0Labels = raw30956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30956 raw30956Labels permutation346 hz
    mixedMoment B raw30956step0 raw30956step0Labels = mixedMoment B raw30956step1 raw30956step1Labels := by
      have ha : raw30956step1 = (fun i j => raw30956step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30956step1 raw30956step0; decide +kernel
      have hl : raw30956step1Labels = raw30956step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30956step0 raw30956step0Labels permutation151 permutation3
    mixedMoment B raw30956step1 raw30956step1Labels = mixedMoment B raw30956step2 raw30956step2Labels := by
      have ha : raw30956step2 = -raw30956step1 := by apply Matrix.ext; change ∀ i j, raw30956step2 i j = -(raw30956step1 i j); unfold raw30956step2 raw30956step1; decide +kernel
      have hl : raw30956step2Labels = raw30956step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30956step2 raw30956step2Labels = mixedMoment B raw30956step3 raw30956step3Labels := by
      have ha : raw30956step3 = raw30956step2 := by apply Matrix.ext; unfold raw30956step3 raw30956step2; decide +kernel
      have hl : raw30956step2Labels = labelEmbedding6 ∘ raw30956step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30956step2 raw30956step2Labels raw30956step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4687 node4687Labels := by rfl

def raw30957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30957 raw30957Labels = mixedMoment B node4872 node4872Labels := by
  calc
    mixedMoment B raw30957 raw30957Labels = mixedMoment B raw30957step0 raw30957step0Labels := by
      have hz : ∀ j, raw30957 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30957step0 = (fun i j => raw30957 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30957step0 raw30957; decide +kernel
      have hl : raw30957step0Labels = raw30957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30957 raw30957Labels permutation434 hz
    mixedMoment B raw30957step0 raw30957step0Labels = mixedMoment B raw30957step1 raw30957step1Labels := by
      have hz : ∀ j, raw30957step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30957step1 = (fun i j => raw30957step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30957step1 raw30957step0; decide +kernel
      have hl : raw30957step1Labels = raw30957step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30957step0 raw30957step0Labels permutation80 hz
    _ = mixedMoment B node4872 node4872Labels := by rfl

def raw30958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30958step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -2, 3], ![-2, 2, 0]]
def raw30958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30958step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw30958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30958 raw30958Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw30958 raw30958Labels = mixedMoment B raw30958step0 raw30958step0Labels := by
      have hz : ∀ j, raw30958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30958step0 = (fun i j => raw30958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30958step0 raw30958; decide +kernel
      have hl : raw30958step0Labels = raw30958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30958 raw30958Labels permutation434 hz
    mixedMoment B raw30958step0 raw30958step0Labels = mixedMoment B raw30958step1 raw30958step1Labels := by
      have hz : ∀ j, raw30958step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30958step1 = (fun i j => raw30958step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30958step1 raw30958step0; decide +kernel
      have hl : raw30958step1Labels = raw30958step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30958step0 raw30958step0Labels permutation80 hz
    mixedMoment B raw30958step1 raw30958step1Labels = mixedMoment B raw30958step2 raw30958step2Labels := by
      have ha : raw30958step2 = (fun i j => raw30958step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30958step2 raw30958step1; decide +kernel
      have hl : raw30958step2Labels = raw30958step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30958step1 raw30958step1Labels permutation12 permutation6
    mixedMoment B raw30958step2 raw30958step2Labels = mixedMoment B raw30958step3 raw30958step3Labels := by
      have ha : raw30958step3 = -raw30958step2 := by apply Matrix.ext; change ∀ i j, raw30958step3 i j = -(raw30958step2 i j); unfold raw30958step3 raw30958step2; decide +kernel
      have hl : raw30958step3Labels = raw30958step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3056 node3056Labels := by rfl

def raw30959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw30959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30959 raw30959Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw30959 raw30959Labels = mixedMoment B raw30959step0 raw30959step0Labels := by
      have hz : ∀ j, raw30959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30959step0 = (fun i j => raw30959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30959step0 raw30959; decide +kernel
      have hl : raw30959step0Labels = raw30959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30959 raw30959Labels permutation434 hz
    mixedMoment B raw30959step0 raw30959step0Labels = mixedMoment B raw30959step1 raw30959step1Labels := by
      have ha : raw30959step1 = (fun i j => raw30959step0 (permutation52 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30959step1 raw30959step0; decide +kernel
      have hl : raw30959step1Labels = raw30959step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30959step0 raw30959step0Labels permutation52 permutation6
    mixedMoment B raw30959step1 raw30959step1Labels = mixedMoment B raw30959step2 raw30959step2Labels := by
      have ha : raw30959step2 = -raw30959step1 := by apply Matrix.ext; change ∀ i j, raw30959step2 i j = -(raw30959step1 i j); unfold raw30959step2 raw30959step1; decide +kernel
      have hl : raw30959step2Labels = raw30959step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3040 node3040Labels := by rfl

def raw30960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw30960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30960 raw30960Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw30960 raw30960Labels = mixedMoment B raw30960step0 raw30960step0Labels := by
      have hz : ∀ j, raw30960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30960step0 = (fun i j => raw30960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30960step0 raw30960; decide +kernel
      have hl : raw30960step0Labels = raw30960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30960 raw30960Labels permutation346 hz
    mixedMoment B raw30960step0 raw30960step0Labels = mixedMoment B raw30960step1 raw30960step1Labels := by
      have ha : raw30960step1 = (fun i j => raw30960step0 (permutation52 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30960step1 raw30960step0; decide +kernel
      have hl : raw30960step1Labels = raw30960step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30960step0 raw30960step0Labels permutation52 permutation6
    mixedMoment B raw30960step1 raw30960step1Labels = mixedMoment B raw30960step2 raw30960step2Labels := by
      have ha : raw30960step2 = -raw30960step1 := by apply Matrix.ext; change ∀ i j, raw30960step2 i j = -(raw30960step1 i j); unfold raw30960step2 raw30960step1; decide +kernel
      have hl : raw30960step2Labels = raw30960step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3040 node3040Labels := by rfl

def raw30961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30961step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw30961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30961step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30961 raw30961Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw30961 raw30961Labels = mixedMoment B raw30961step0 raw30961step0Labels := by
      have hz : ∀ j, raw30961 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30961step0 = (fun i j => raw30961 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30961step0 raw30961; decide +kernel
      have hl : raw30961step0Labels = raw30961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30961 raw30961Labels permutation434 hz
    mixedMoment B raw30961step0 raw30961step0Labels = mixedMoment B raw30961step1 raw30961step1Labels := by
      have hz : ∀ j, raw30961step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30961step1 = (fun i j => raw30961step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30961step1 raw30961step0; decide +kernel
      have hl : raw30961step1Labels = raw30961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30961step0 raw30961step0Labels permutation80 hz
    mixedMoment B raw30961step1 raw30961step1Labels = mixedMoment B raw30961step2 raw30961step2Labels := by
      have ha : raw30961step2 = (fun i j => raw30961step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30961step2 raw30961step1; decide +kernel
      have hl : raw30961step2Labels = raw30961step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30961step1 raw30961step1Labels permutation12 permutation6
    mixedMoment B raw30961step2 raw30961step2Labels = mixedMoment B raw30961step3 raw30961step3Labels := by
      have ha : raw30961step3 = -raw30961step2 := by apply Matrix.ext; change ∀ i j, raw30961step3 i j = -(raw30961step2 i j); unfold raw30961step3 raw30961step2; decide +kernel
      have hl : raw30961step3Labels = raw30961step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw30962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw30962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30962step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw30962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30962 raw30962Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw30962 raw30962Labels = mixedMoment B raw30962step0 raw30962step0Labels := by
      have hz : ∀ j, raw30962 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30962step0 = (fun i j => raw30962 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30962step0 raw30962; decide +kernel
      have hl : raw30962step0Labels = raw30962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30962 raw30962Labels permutation434 hz
    mixedMoment B raw30962step0 raw30962step0Labels = mixedMoment B raw30962step1 raw30962step1Labels := by
      have hz : ∀ j, raw30962step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30962step1 = (fun i j => raw30962step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30962step1 raw30962step0; decide +kernel
      have hl : raw30962step1Labels = raw30962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30962step0 raw30962step0Labels permutation80 hz
    mixedMoment B raw30962step1 raw30962step1Labels = mixedMoment B raw30962step2 raw30962step2Labels := by
      have ha : raw30962step2 = (fun i j => raw30962step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30962step2 raw30962step1; decide +kernel
      have hl : raw30962step2Labels = raw30962step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30962step1 raw30962step1Labels permutation12 permutation6
    mixedMoment B raw30962step2 raw30962step2Labels = mixedMoment B raw30962step3 raw30962step3Labels := by
      have ha : raw30962step3 = -raw30962step2 := by apply Matrix.ext; change ∀ i j, raw30962step3 i j = -(raw30962step2 i j); unfold raw30962step3 raw30962step2; decide +kernel
      have hl : raw30962step3Labels = raw30962step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw30963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30963step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30963 raw30963Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw30963 raw30963Labels = mixedMoment B raw30963step0 raw30963step0Labels := by
      have hz : ∀ j, raw30963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30963step0 = (fun i j => raw30963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30963step0 raw30963; decide +kernel
      have hl : raw30963step0Labels = raw30963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30963 raw30963Labels permutation434 hz
    mixedMoment B raw30963step0 raw30963step0Labels = mixedMoment B raw30963step1 raw30963step1Labels := by
      have hz : ∀ j, raw30963step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30963step1 = (fun i j => raw30963step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30963step1 raw30963step0; decide +kernel
      have hl : raw30963step1Labels = raw30963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30963step0 raw30963step0Labels permutation80 hz
    mixedMoment B raw30963step1 raw30963step1Labels = mixedMoment B raw30963step2 raw30963step2Labels := by
      have ha : raw30963step2 = (fun i j => raw30963step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30963step2 raw30963step1; decide +kernel
      have hl : raw30963step2Labels = raw30963step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30963step1 raw30963step1Labels permutation8 permutation3
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw30964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30964 raw30964Labels = mixedMoment B node3131 node3131Labels := by
  calc
    mixedMoment B raw30964 raw30964Labels = mixedMoment B raw30964step0 raw30964step0Labels := by
      have hz : ∀ j, raw30964 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30964step0 = (fun i j => raw30964 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30964step0 raw30964; decide +kernel
      have hl : raw30964step0Labels = raw30964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30964 raw30964Labels permutation434 hz
    mixedMoment B raw30964step0 raw30964step0Labels = mixedMoment B raw30964step1 raw30964step1Labels := by
      have ha : raw30964step1 = (fun i j => raw30964step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30964step1 raw30964step0; decide +kernel
      have hl : raw30964step1Labels = raw30964step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30964step0 raw30964step0Labels permutation32 permutation3
    _ = mixedMoment B node3131 node3131Labels := by rfl

def raw30965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30965 raw30965Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw30965 raw30965Labels = mixedMoment B raw30965step0 raw30965step0Labels := by
      have ha : raw30965step0 = (fun i j => raw30965 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30965step0 raw30965; decide +kernel
      have hl : raw30965step0Labels = raw30965Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30965 raw30965Labels permutation158 permutation3
    _ = mixedMoment B node3163 node3163Labels := by rfl

def raw30966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30966 raw30966Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw30966 raw30966Labels = mixedMoment B raw30966step0 raw30966step0Labels := by
      have hz : ∀ j, raw30966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30966step0 = (fun i j => raw30966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30966step0 raw30966; decide +kernel
      have hl : raw30966step0Labels = raw30966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30966 raw30966Labels permutation434 hz
    mixedMoment B raw30966step0 raw30966step0Labels = mixedMoment B raw30966step1 raw30966step1Labels := by
      have ha : raw30966step1 = (fun i j => raw30966step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30966step1 raw30966step0; decide +kernel
      have hl : raw30966step1Labels = raw30966step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30966step0 raw30966step0Labels permutation34 permutation3
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw30967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw30967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30967 raw30967Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw30967 raw30967Labels = mixedMoment B raw30967step0 raw30967step0Labels := by
      have hz : ∀ j, raw30967 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30967step0 = (fun i j => raw30967 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30967step0 raw30967; decide +kernel
      have hl : raw30967step0Labels = raw30967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30967 raw30967Labels permutation434 hz
    mixedMoment B raw30967step0 raw30967step0Labels = mixedMoment B raw30967step1 raw30967step1Labels := by
      have ha : raw30967step1 = (fun i j => raw30967step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30967step1 raw30967step0; decide +kernel
      have hl : raw30967step1Labels = raw30967step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30967step0 raw30967step0Labels permutation33 permutation3
    _ = mixedMoment B node3185 node3185Labels := by rfl

def raw30968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30968 raw30968Labels = mixedMoment B node3131 node3131Labels := by
  calc
    mixedMoment B raw30968 raw30968Labels = mixedMoment B raw30968step0 raw30968step0Labels := by
      have hz : ∀ j, raw30968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30968step0 = (fun i j => raw30968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30968step0 raw30968; decide +kernel
      have hl : raw30968step0Labels = raw30968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30968 raw30968Labels permutation346 hz
    mixedMoment B raw30968step0 raw30968step0Labels = mixedMoment B raw30968step1 raw30968step1Labels := by
      have ha : raw30968step1 = (fun i j => raw30968step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30968step1 raw30968step0; decide +kernel
      have hl : raw30968step1Labels = raw30968step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30968step0 raw30968step0Labels permutation32 permutation3
    _ = mixedMoment B node3131 node3131Labels := by rfl

def raw30969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30969 raw30969Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw30969 raw30969Labels = mixedMoment B raw30969step0 raw30969step0Labels := by
      have ha : raw30969step0 = (fun i j => raw30969 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30969step0 raw30969; decide +kernel
      have hl : raw30969step0Labels = raw30969Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30969 raw30969Labels permutation152 permutation3
    _ = mixedMoment B node3163 node3163Labels := by rfl

def raw30970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30970 raw30970Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw30970 raw30970Labels = mixedMoment B raw30970step0 raw30970step0Labels := by
      have hz : ∀ j, raw30970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30970step0 = (fun i j => raw30970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30970step0 raw30970; decide +kernel
      have hl : raw30970step0Labels = raw30970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30970 raw30970Labels permutation346 hz
    mixedMoment B raw30970step0 raw30970step0Labels = mixedMoment B raw30970step1 raw30970step1Labels := by
      have ha : raw30970step1 = (fun i j => raw30970step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30970step1 raw30970step0; decide +kernel
      have hl : raw30970step1Labels = raw30970step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30970step0 raw30970step0Labels permutation34 permutation3
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw30971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw30971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30971 raw30971Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw30971 raw30971Labels = mixedMoment B raw30971step0 raw30971step0Labels := by
      have hz : ∀ j, raw30971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30971step0 = (fun i j => raw30971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30971step0 raw30971; decide +kernel
      have hl : raw30971step0Labels = raw30971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30971 raw30971Labels permutation346 hz
    mixedMoment B raw30971step0 raw30971step0Labels = mixedMoment B raw30971step1 raw30971step1Labels := by
      have ha : raw30971step1 = (fun i j => raw30971step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30971step1 raw30971step0; decide +kernel
      have hl : raw30971step1Labels = raw30971step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30971step0 raw30971step0Labels permutation33 permutation3
    _ = mixedMoment B node3185 node3185Labels := by rfl

def raw30972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30972step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-2, -1, 3], ![-3, 3, 0]]
def raw30972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw30972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30972 raw30972Labels = mixedMoment B node2821 node2821Labels := by
  calc
    mixedMoment B raw30972 raw30972Labels = mixedMoment B raw30972step0 raw30972step0Labels := by
      have hz : ∀ j, raw30972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30972step0 = (fun i j => raw30972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30972step0 raw30972; decide +kernel
      have hl : raw30972step0Labels = raw30972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30972 raw30972Labels permutation434 hz
    mixedMoment B raw30972step0 raw30972step0Labels = mixedMoment B raw30972step1 raw30972step1Labels := by
      have hz : ∀ j, raw30972step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30972step1 = (fun i j => raw30972step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30972step1 raw30972step0; decide +kernel
      have hl : raw30972step1Labels = raw30972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30972step0 raw30972step0Labels permutation80 hz
    mixedMoment B raw30972step1 raw30972step1Labels = mixedMoment B raw30972step2 raw30972step2Labels := by
      have ha : raw30972step2 = (fun i j => raw30972step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30972step2 raw30972step1; decide +kernel
      have hl : raw30972step2Labels = raw30972step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30972step1 raw30972step1Labels permutation25 permutation3
    mixedMoment B raw30972step2 raw30972step2Labels = mixedMoment B raw30972step3 raw30972step3Labels := by
      have ha : raw30972step3 = -raw30972step2 := by apply Matrix.ext; change ∀ i j, raw30972step3 i j = -(raw30972step2 i j); unfold raw30972step3 raw30972step2; decide +kernel
      have hl : raw30972step3Labels = raw30972step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2821 node2821Labels := by rfl

def raw30973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30973step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30973step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30973 raw30973Labels = mixedMoment B node2816 node2816Labels := by
  calc
    mixedMoment B raw30973 raw30973Labels = mixedMoment B raw30973step0 raw30973step0Labels := by
      have hz : ∀ j, raw30973 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30973step0 = (fun i j => raw30973 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30973step0 raw30973; decide +kernel
      have hl : raw30973step0Labels = raw30973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30973 raw30973Labels permutation434 hz
    mixedMoment B raw30973step0 raw30973step0Labels = mixedMoment B raw30973step1 raw30973step1Labels := by
      have ha : raw30973step1 = (fun i j => raw30973step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30973step1 raw30973step0; decide +kernel
      have hl : raw30973step1Labels = raw30973step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30973step0 raw30973step0Labels permutation127 permutation3
    mixedMoment B raw30973step1 raw30973step1Labels = mixedMoment B raw30973step2 raw30973step2Labels := by
      have ha : raw30973step2 = -raw30973step1 := by apply Matrix.ext; change ∀ i j, raw30973step2 i j = -(raw30973step1 i j); unfold raw30973step2 raw30973step1; decide +kernel
      have hl : raw30973step2Labels = raw30973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2816 node2816Labels := by rfl

def raw30974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30974step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30974 raw30974Labels = mixedMoment B node2816 node2816Labels := by
  calc
    mixedMoment B raw30974 raw30974Labels = mixedMoment B raw30974step0 raw30974step0Labels := by
      have hz : ∀ j, raw30974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30974step0 = (fun i j => raw30974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30974step0 raw30974; decide +kernel
      have hl : raw30974step0Labels = raw30974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30974 raw30974Labels permutation346 hz
    mixedMoment B raw30974step0 raw30974step0Labels = mixedMoment B raw30974step1 raw30974step1Labels := by
      have ha : raw30974step1 = (fun i j => raw30974step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30974step1 raw30974step0; decide +kernel
      have hl : raw30974step1Labels = raw30974step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30974step0 raw30974step0Labels permutation127 permutation3
    mixedMoment B raw30974step1 raw30974step1Labels = mixedMoment B raw30974step2 raw30974step2Labels := by
      have ha : raw30974step2 = -raw30974step1 := by apply Matrix.ext; change ∀ i j, raw30974step2 i j = -(raw30974step1 i j); unfold raw30974step2 raw30974step1; decide +kernel
      have hl : raw30974step2Labels = raw30974step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2816 node2816Labels := by rfl

def raw30975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![3, -1, -2], ![1, -1, 0]]
def raw30975step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw30975step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30975 raw30975Labels = mixedMoment B node2966 node2966Labels := by
  calc
    mixedMoment B raw30975 raw30975Labels = mixedMoment B raw30975step0 raw30975step0Labels := by
      have hz : ∀ j, raw30975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30975step0 = (fun i j => raw30975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30975step0 raw30975; decide +kernel
      have hl : raw30975step0Labels = raw30975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30975 raw30975Labels permutation434 hz
    mixedMoment B raw30975step0 raw30975step0Labels = mixedMoment B raw30975step1 raw30975step1Labels := by
      have hz : ∀ j, raw30975step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30975step1 = (fun i j => raw30975step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30975step1 raw30975step0; decide +kernel
      have hl : raw30975step1Labels = raw30975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30975step0 raw30975step0Labels permutation80 hz
    mixedMoment B raw30975step1 raw30975step1Labels = mixedMoment B raw30975step2 raw30975step2Labels := by
      have ha : raw30975step2 = (fun i j => raw30975step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30975step2 raw30975step1; decide +kernel
      have hl : raw30975step2Labels = raw30975step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30975step1 raw30975step1Labels permutation25 permutation3
    mixedMoment B raw30975step2 raw30975step2Labels = mixedMoment B raw30975step3 raw30975step3Labels := by
      have ha : raw30975step3 = -raw30975step2 := by apply Matrix.ext; change ∀ i j, raw30975step3 i j = -(raw30975step2 i j); unfold raw30975step3 raw30975step2; decide +kernel
      have hl : raw30975step3Labels = raw30975step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2966 node2966Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
