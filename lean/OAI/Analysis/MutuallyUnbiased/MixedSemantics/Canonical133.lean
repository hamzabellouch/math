import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw17024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17024step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw17024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17024 raw17024Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw17024 raw17024Labels = mixedMoment B raw17024step0 raw17024step0Labels := by
      have ha : raw17024step0 = (fun i j => raw17024 (permutation435 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17024step0 raw17024; decide +kernel
      have hl : raw17024step0Labels = raw17024Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17024 raw17024Labels permutation435 permutation4
    mixedMoment B raw17024step0 raw17024step0Labels = mixedMoment B raw17024step1 raw17024step1Labels := by
      have ha : raw17024step1 = -raw17024step0 := by apply Matrix.ext; change ∀ i j, raw17024step1 i j = -(raw17024step0 i j); unfold raw17024step1 raw17024step0; decide +kernel
      have hl : raw17024step1Labels = raw17024step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3909 node3909Labels := by rfl

def raw17025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17025 raw17025Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw17025 raw17025Labels = mixedMoment B raw17025step0 raw17025step0Labels := by
      have ha : raw17025step0 = (fun i j => raw17025 (permutation442 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17025step0 raw17025; decide +kernel
      have hl : raw17025step0Labels = raw17025Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17025 raw17025Labels permutation442 permutation4
    mixedMoment B raw17025step0 raw17025step0Labels = mixedMoment B raw17025step1 raw17025step1Labels := by
      have ha : raw17025step1 = -raw17025step0 := by apply Matrix.ext; change ∀ i j, raw17025step1 i j = -(raw17025step0 i j); unfold raw17025step1 raw17025step0; decide +kernel
      have hl : raw17025step1Labels = raw17025step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw17026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17026 raw17026Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw17026 raw17026Labels = mixedMoment B raw17026step0 raw17026step0Labels := by
      have ha : raw17026step0 = (fun i j => raw17026 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17026step0 raw17026; decide +kernel
      have hl : raw17026step0Labels = raw17026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17026 raw17026Labels permutation662 permutation2
    mixedMoment B raw17026step0 raw17026step0Labels = mixedMoment B raw17026step1 raw17026step1Labels := by
      have ha : raw17026step1 = -raw17026step0 := by apply Matrix.ext; change ∀ i j, raw17026step1 i j = -(raw17026step0 i j); unfold raw17026step1 raw17026step0; decide +kernel
      have hl : raw17026step1Labels = raw17026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3945 node3945Labels := by rfl

def raw17027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw17027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw17027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw17027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17027 raw17027Labels = mixedMoment B node3878 node3878Labels := by
  calc
    mixedMoment B raw17027 raw17027Labels = mixedMoment B raw17027step0 raw17027step0Labels := by
      have ha : raw17027step0 = (fun i j => raw17027 (permutation435 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17027step0 raw17027; decide +kernel
      have hl : raw17027step0Labels = raw17027Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17027 raw17027Labels permutation435 permutation4
    mixedMoment B raw17027step0 raw17027step0Labels = mixedMoment B raw17027step1 raw17027step1Labels := by
      have ha : raw17027step1 = -raw17027step0 := by apply Matrix.ext; change ∀ i j, raw17027step1 i j = -(raw17027step0 i j); unfold raw17027step1 raw17027step0; decide +kernel
      have hl : raw17027step1Labels = raw17027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3878 node3878Labels := by rfl

def raw17028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw17028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17028 raw17028Labels = mixedMoment B node2976 node2976Labels := by
  calc
    mixedMoment B raw17028 raw17028Labels = mixedMoment B raw17028step0 raw17028step0Labels := by
      have ha : raw17028step0 = (fun i j => raw17028 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17028step0 raw17028; decide +kernel
      have hl : raw17028step0Labels = raw17028Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17028 raw17028Labels permutation686 permutation2
    mixedMoment B raw17028step0 raw17028step0Labels = mixedMoment B raw17028step1 raw17028step1Labels := by
      have ha : raw17028step1 = -raw17028step0 := by apply Matrix.ext; change ∀ i j, raw17028step1 i j = -(raw17028step0 i j); unfold raw17028step1 raw17028step0; decide +kernel
      have hl : raw17028step1Labels = raw17028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2976 node2976Labels := by rfl

def raw17029 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17029 raw17029Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw17029 raw17029Labels = mixedMoment B raw17029step0 raw17029step0Labels := by
      have ha : raw17029step0 = (fun i j => raw17029 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17029step0 raw17029; decide +kernel
      have hl : raw17029step0Labels = raw17029Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17029 raw17029Labels permutation200 permutation2
    mixedMoment B raw17029step0 raw17029step0Labels = mixedMoment B raw17029step1 raw17029step1Labels := by
      have ha : raw17029step1 = -raw17029step0 := by apply Matrix.ext; change ∀ i j, raw17029step1 i j = -(raw17029step0 i j); unfold raw17029step1 raw17029step0; decide +kernel
      have hl : raw17029step1Labels = raw17029step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5382 node5382Labels := by rfl

def raw17030 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17030 raw17030Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw17030 raw17030Labels = mixedMoment B raw17030step0 raw17030step0Labels := by
      have ha : raw17030step0 = (fun i j => raw17030 (permutation203 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17030step0 raw17030; decide +kernel
      have hl : raw17030step0Labels = raw17030Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17030 raw17030Labels permutation203 permutation2
    mixedMoment B raw17030step0 raw17030step0Labels = mixedMoment B raw17030step1 raw17030step1Labels := by
      have ha : raw17030step1 = -raw17030step0 := by apply Matrix.ext; change ∀ i j, raw17030step1 i j = -(raw17030step0 i j); unfold raw17030step1 raw17030step0; decide +kernel
      have hl : raw17030step1Labels = raw17030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw17031 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17031step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17031 raw17031Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17031 raw17031Labels = mixedMoment B raw17031step0 raw17031step0Labels := by
      have ha : raw17031step0 = (fun i j => raw17031 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17031step0 raw17031; decide +kernel
      have hl : raw17031step0Labels = raw17031Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17031 raw17031Labels permutation158 permutation7
    mixedMoment B raw17031step0 raw17031step0Labels = mixedMoment B raw17031step1 raw17031step1Labels := by
      have ha : raw17031step1 = raw17031step0 := by apply Matrix.ext; unfold raw17031step1 raw17031step0; decide +kernel
      have hl : raw17031step0Labels = labelEmbedding10 ∘ raw17031step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17031step0 raw17031step0Labels raw17031step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17032 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17032 raw17032Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw17032 raw17032Labels = mixedMoment B raw17032step0 raw17032step0Labels := by
      have ha : raw17032step0 = (fun i j => raw17032 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17032step0 raw17032; decide +kernel
      have hl : raw17032step0Labels = raw17032Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17032 raw17032Labels permutation201 permutation2
    mixedMoment B raw17032step0 raw17032step0Labels = mixedMoment B raw17032step1 raw17032step1Labels := by
      have ha : raw17032step1 = -raw17032step0 := by apply Matrix.ext; change ∀ i j, raw17032step1 i j = -(raw17032step0 i j); unfold raw17032step1 raw17032step0; decide +kernel
      have hl : raw17032step1Labels = raw17032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw17033 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17033 raw17033Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw17033 raw17033Labels = mixedMoment B raw17033step0 raw17033step0Labels := by
      have ha : raw17033step0 = (fun i j => raw17033 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17033step0 raw17033; decide +kernel
      have hl : raw17033step0Labels = raw17033Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17033 raw17033Labels permutation200 permutation2
    mixedMoment B raw17033step0 raw17033step0Labels = mixedMoment B raw17033step1 raw17033step1Labels := by
      have ha : raw17033step1 = -raw17033step0 := by apply Matrix.ext; change ∀ i j, raw17033step1 i j = -(raw17033step0 i j); unfold raw17033step1 raw17033step0; decide +kernel
      have hl : raw17033step1Labels = raw17033step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw17034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17034step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17034 raw17034Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw17034 raw17034Labels = mixedMoment B raw17034step0 raw17034step0Labels := by
      have ha : raw17034step0 = (fun i j => raw17034 (permutation409 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17034step0 raw17034; decide +kernel
      have hl : raw17034step0Labels = raw17034Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17034 raw17034Labels permutation409 permutation3
    mixedMoment B raw17034step0 raw17034step0Labels = mixedMoment B raw17034step1 raw17034step1Labels := by
      have ha : raw17034step1 = raw17034step0 := by apply Matrix.ext; unfold raw17034step1 raw17034step0; decide +kernel
      have hl : raw17034step0Labels = labelEmbedding6 ∘ raw17034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17034step0 raw17034step0Labels raw17034step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5420 node5420Labels := by rfl

def raw17035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17035step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17035step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17035step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17035 raw17035Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw17035 raw17035Labels = mixedMoment B raw17035step0 raw17035step0Labels := by
      have ha : raw17035step0 = (fun i j => raw17035 (permutation455 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17035step0 raw17035; decide +kernel
      have hl : raw17035step0Labels = raw17035Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17035 raw17035Labels permutation455 permutation3
    mixedMoment B raw17035step0 raw17035step0Labels = mixedMoment B raw17035step1 raw17035step1Labels := by
      have ha : raw17035step1 = -raw17035step0 := by apply Matrix.ext; change ∀ i j, raw17035step1 i j = -(raw17035step0 i j); unfold raw17035step1 raw17035step0; decide +kernel
      have hl : raw17035step1Labels = raw17035step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17035step1 raw17035step1Labels = mixedMoment B raw17035step2 raw17035step2Labels := by
      have ha : raw17035step2 = raw17035step1 := by apply Matrix.ext; unfold raw17035step2 raw17035step1; decide +kernel
      have hl : raw17035step1Labels = labelEmbedding6 ∘ raw17035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17035step1 raw17035step1Labels raw17035step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw17036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17036 raw17036Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw17036 raw17036Labels = mixedMoment B raw17036step0 raw17036step0Labels := by
      have ha : raw17036step0 = (fun i j => raw17036 (permutation679 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17036step0 raw17036; decide +kernel
      have hl : raw17036step0Labels = raw17036Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17036 raw17036Labels permutation679 permutation2
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw17037 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17037step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17037step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17037step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17037step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17037 raw17037Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw17037 raw17037Labels = mixedMoment B raw17037step0 raw17037step0Labels := by
      have hz : ∀ j, raw17037 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17037step0 = (fun i j => raw17037 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17037step0 raw17037; decide +kernel
      have hl : raw17037step0Labels = raw17037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17037 raw17037Labels permutation346 hz
    mixedMoment B raw17037step0 raw17037step0Labels = mixedMoment B raw17037step1 raw17037step1Labels := by
      have ha : raw17037step1 = (fun i j => raw17037step0 (permutation81 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17037step1 raw17037step0; decide +kernel
      have hl : raw17037step1Labels = raw17037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17037step0 raw17037step0Labels permutation81 permutation3
    mixedMoment B raw17037step1 raw17037step1Labels = mixedMoment B raw17037step2 raw17037step2Labels := by
      have ha : raw17037step2 = -raw17037step1 := by apply Matrix.ext; change ∀ i j, raw17037step2 i j = -(raw17037step1 i j); unfold raw17037step2 raw17037step1; decide +kernel
      have hl : raw17037step2Labels = raw17037step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17037step2 raw17037step2Labels = mixedMoment B raw17037step3 raw17037step3Labels := by
      have ha : raw17037step3 = raw17037step2 := by apply Matrix.ext; unfold raw17037step3 raw17037step2; decide +kernel
      have hl : raw17037step2Labels = labelEmbedding6 ∘ raw17037step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17037step2 raw17037step2Labels raw17037step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw17038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17038 raw17038Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw17038 raw17038Labels = mixedMoment B raw17038step0 raw17038step0Labels := by
      have hz : ∀ j, raw17038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17038step0 = (fun i j => raw17038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17038step0 raw17038; decide +kernel
      have hl : raw17038step0Labels = raw17038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17038 raw17038Labels permutation346 hz
    mixedMoment B raw17038step0 raw17038step0Labels = mixedMoment B raw17038step1 raw17038step1Labels := by
      have ha : raw17038step1 = (fun i j => raw17038step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17038step1 raw17038step0; decide +kernel
      have hl : raw17038step1Labels = raw17038step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17038step0 raw17038step0Labels permutation148 permutation2
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw17039 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17039step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17039 raw17039Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw17039 raw17039Labels = mixedMoment B raw17039step0 raw17039step0Labels := by
      have ha : raw17039step0 = (fun i j => raw17039 (permutation517 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17039step0 raw17039; decide +kernel
      have hl : raw17039step0Labels = raw17039Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17039 raw17039Labels permutation517 permutation5
    mixedMoment B raw17039step0 raw17039step0Labels = mixedMoment B raw17039step1 raw17039step1Labels := by
      have ha : raw17039step1 = raw17039step0 := by apply Matrix.ext; unfold raw17039step1 raw17039step0; decide +kernel
      have hl : raw17039step0Labels = labelEmbedding8 ∘ raw17039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17039step0 raw17039step0Labels raw17039step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw17040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17040step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17040step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17040 raw17040Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw17040 raw17040Labels = mixedMoment B raw17040step0 raw17040step0Labels := by
      have ha : raw17040step0 = (fun i j => raw17040 (permutation515 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17040step0 raw17040; decide +kernel
      have hl : raw17040step0Labels = raw17040Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17040 raw17040Labels permutation515 permutation5
    mixedMoment B raw17040step0 raw17040step0Labels = mixedMoment B raw17040step1 raw17040step1Labels := by
      have ha : raw17040step1 = raw17040step0 := by apply Matrix.ext; unfold raw17040step1 raw17040step0; decide +kernel
      have hl : raw17040step0Labels = labelEmbedding8 ∘ raw17040step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17040step0 raw17040step0Labels raw17040step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

def raw17041 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17041step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17041step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17041step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17041step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17041 raw17041Labels = mixedMoment B node4848 node4848Labels := by
  calc
    mixedMoment B raw17041 raw17041Labels = mixedMoment B raw17041step0 raw17041step0Labels := by
      have ha : raw17041step0 = (fun i j => raw17041 (permutation439 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17041step0 raw17041; decide +kernel
      have hl : raw17041step0Labels = raw17041Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17041 raw17041Labels permutation439 permutation3
    mixedMoment B raw17041step0 raw17041step0Labels = mixedMoment B raw17041step1 raw17041step1Labels := by
      have ha : raw17041step1 = -raw17041step0 := by apply Matrix.ext; change ∀ i j, raw17041step1 i j = -(raw17041step0 i j); unfold raw17041step1 raw17041step0; decide +kernel
      have hl : raw17041step1Labels = raw17041step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17041step1 raw17041step1Labels = mixedMoment B raw17041step2 raw17041step2Labels := by
      have ha : raw17041step2 = raw17041step1 := by apply Matrix.ext; unfold raw17041step2 raw17041step1; decide +kernel
      have hl : raw17041step1Labels = labelEmbedding6 ∘ raw17041step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17041step1 raw17041step1Labels raw17041step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4848 node4848Labels := by rfl

def raw17042 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17042step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17042step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17042step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17042step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17042 raw17042Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw17042 raw17042Labels = mixedMoment B raw17042step0 raw17042step0Labels := by
      have ha : raw17042step0 = (fun i j => raw17042 (permutation438 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17042step0 raw17042; decide +kernel
      have hl : raw17042step0Labels = raw17042Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17042 raw17042Labels permutation438 permutation3
    mixedMoment B raw17042step0 raw17042step0Labels = mixedMoment B raw17042step1 raw17042step1Labels := by
      have ha : raw17042step1 = -raw17042step0 := by apply Matrix.ext; change ∀ i j, raw17042step1 i j = -(raw17042step0 i j); unfold raw17042step1 raw17042step0; decide +kernel
      have hl : raw17042step1Labels = raw17042step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17042step1 raw17042step1Labels = mixedMoment B raw17042step2 raw17042step2Labels := by
      have ha : raw17042step2 = raw17042step1 := by apply Matrix.ext; unfold raw17042step2 raw17042step1; decide +kernel
      have hl : raw17042step1Labels = labelEmbedding6 ∘ raw17042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17042step1 raw17042step1Labels raw17042step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

def raw17043 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw17043step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17043step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17043step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17043 raw17043Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw17043 raw17043Labels = mixedMoment B raw17043step0 raw17043step0Labels := by
      have ha : raw17043step0 = (fun i j => raw17043 (permutation436 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17043step0 raw17043; decide +kernel
      have hl : raw17043step0Labels = raw17043Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17043 raw17043Labels permutation436 permutation3
    mixedMoment B raw17043step0 raw17043step0Labels = mixedMoment B raw17043step1 raw17043step1Labels := by
      have ha : raw17043step1 = -raw17043step0 := by apply Matrix.ext; change ∀ i j, raw17043step1 i j = -(raw17043step0 i j); unfold raw17043step1 raw17043step0; decide +kernel
      have hl : raw17043step1Labels = raw17043step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17043step1 raw17043step1Labels = mixedMoment B raw17043step2 raw17043step2Labels := by
      have ha : raw17043step2 = raw17043step1 := by apply Matrix.ext; unfold raw17043step2 raw17043step1; decide +kernel
      have hl : raw17043step1Labels = labelEmbedding6 ∘ raw17043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17043step1 raw17043step1Labels raw17043step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw17044 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17044step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17044step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17044 raw17044Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw17044 raw17044Labels = mixedMoment B raw17044step0 raw17044step0Labels := by
      have ha : raw17044step0 = (fun i j => raw17044 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17044step0 raw17044; decide +kernel
      have hl : raw17044step0Labels = raw17044Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17044 raw17044Labels permutation155 permutation4
    mixedMoment B raw17044step0 raw17044step0Labels = mixedMoment B raw17044step1 raw17044step1Labels := by
      have ha : raw17044step1 = -raw17044step0 := by apply Matrix.ext; change ∀ i j, raw17044step1 i j = -(raw17044step0 i j); unfold raw17044step1 raw17044step0; decide +kernel
      have hl : raw17044step1Labels = raw17044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17044step1 raw17044step1Labels = mixedMoment B raw17044step2 raw17044step2Labels := by
      have ha : raw17044step2 = raw17044step1 := by apply Matrix.ext; unfold raw17044step2 raw17044step1; decide +kernel
      have hl : raw17044step1Labels = labelEmbedding7 ∘ raw17044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17044step1 raw17044step1Labels raw17044step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw17045 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17045step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17045 raw17045Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw17045 raw17045Labels = mixedMoment B raw17045step0 raw17045step0Labels := by
      have ha : raw17045step0 = (fun i j => raw17045 (permutation500 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17045step0 raw17045; decide +kernel
      have hl : raw17045step0Labels = raw17045Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17045 raw17045Labels permutation500 permutation5
    mixedMoment B raw17045step0 raw17045step0Labels = mixedMoment B raw17045step1 raw17045step1Labels := by
      have ha : raw17045step1 = raw17045step0 := by apply Matrix.ext; unfold raw17045step1 raw17045step0; decide +kernel
      have hl : raw17045step0Labels = labelEmbedding8 ∘ raw17045step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17045step0 raw17045step0Labels raw17045step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw17046 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17046step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17046 raw17046Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw17046 raw17046Labels = mixedMoment B raw17046step0 raw17046step0Labels := by
      have ha : raw17046step0 = (fun i j => raw17046 (permutation499 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17046step0 raw17046; decide +kernel
      have hl : raw17046step0Labels = raw17046Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17046 raw17046Labels permutation499 permutation5
    mixedMoment B raw17046step0 raw17046step0Labels = mixedMoment B raw17046step1 raw17046step1Labels := by
      have ha : raw17046step1 = raw17046step0 := by apply Matrix.ext; unfold raw17046step1 raw17046step0; decide +kernel
      have hl : raw17046step0Labels = labelEmbedding8 ∘ raw17046step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17046step0 raw17046step0Labels raw17046step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5420 node5420Labels := by rfl

def raw17047 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17047step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17047 raw17047Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw17047 raw17047Labels = mixedMoment B raw17047step0 raw17047step0Labels := by
      have ha : raw17047step0 = (fun i j => raw17047 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17047step0 raw17047; decide +kernel
      have hl : raw17047step0Labels = raw17047Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17047 raw17047Labels permutation152 permutation6
    mixedMoment B raw17047step0 raw17047step0Labels = mixedMoment B raw17047step1 raw17047step1Labels := by
      have ha : raw17047step1 = raw17047step0 := by apply Matrix.ext; unfold raw17047step1 raw17047step0; decide +kernel
      have hl : raw17047step0Labels = labelEmbedding9 ∘ raw17047step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17047step0 raw17047step0Labels raw17047step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw17048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17048 raw17048Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17048 raw17048Labels = mixedMoment B raw17048step0 raw17048step0Labels := by
      have ha : raw17048step0 = (fun i j => raw17048 (permutation643 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17048step0 raw17048; decide +kernel
      have hl : raw17048step0Labels = raw17048Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17048 raw17048Labels permutation643 permutation2
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw17049 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17049step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17049 raw17049Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw17049 raw17049Labels = mixedMoment B raw17049step0 raw17049step0Labels := by
      have ha : raw17049step0 = (fun i j => raw17049 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17049step0 raw17049; decide +kernel
      have hl : raw17049step0Labels = raw17049Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17049 raw17049Labels permutation664 permutation4
    mixedMoment B raw17049step0 raw17049step0Labels = mixedMoment B raw17049step1 raw17049step1Labels := by
      have ha : raw17049step1 = raw17049step0 := by apply Matrix.ext; unfold raw17049step1 raw17049step0; decide +kernel
      have hl : raw17049step0Labels = labelEmbedding7 ∘ raw17049step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17049step0 raw17049step0Labels raw17049step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw17050 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17050step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17050 raw17050Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw17050 raw17050Labels = mixedMoment B raw17050step0 raw17050step0Labels := by
      have ha : raw17050step0 = (fun i j => raw17050 (permutation663 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17050step0 raw17050; decide +kernel
      have hl : raw17050step0Labels = raw17050Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17050 raw17050Labels permutation663 permutation4
    mixedMoment B raw17050step0 raw17050step0Labels = mixedMoment B raw17050step1 raw17050step1Labels := by
      have ha : raw17050step1 = raw17050step0 := by apply Matrix.ext; unfold raw17050step1 raw17050step0; decide +kernel
      have hl : raw17050step0Labels = labelEmbedding7 ∘ raw17050step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17050step0 raw17050step0Labels raw17050step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw17051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17051step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17051step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17051 raw17051Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw17051 raw17051Labels = mixedMoment B raw17051step0 raw17051step0Labels := by
      have ha : raw17051step0 = (fun i j => raw17051 (permutation661 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17051step0 raw17051; decide +kernel
      have hl : raw17051step0Labels = raw17051Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17051 raw17051Labels permutation661 permutation4
    mixedMoment B raw17051step0 raw17051step0Labels = mixedMoment B raw17051step1 raw17051step1Labels := by
      have ha : raw17051step1 = raw17051step0 := by apply Matrix.ext; unfold raw17051step1 raw17051step0; decide +kernel
      have hl : raw17051step0Labels = labelEmbedding7 ∘ raw17051step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17051step0 raw17051step0Labels raw17051step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw17052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17052step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17052step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17052 raw17052Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17052 raw17052Labels = mixedMoment B raw17052step0 raw17052step0Labels := by
      have ha : raw17052step0 = (fun i j => raw17052 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17052step0 raw17052; decide +kernel
      have hl : raw17052step0Labels = raw17052Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17052 raw17052Labels permutation688 permutation6
    mixedMoment B raw17052step0 raw17052step0Labels = mixedMoment B raw17052step1 raw17052step1Labels := by
      have ha : raw17052step1 = -raw17052step0 := by apply Matrix.ext; change ∀ i j, raw17052step1 i j = -(raw17052step0 i j); unfold raw17052step1 raw17052step0; decide +kernel
      have hl : raw17052step1Labels = raw17052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17052step1 raw17052step1Labels = mixedMoment B raw17052step2 raw17052step2Labels := by
      have ha : raw17052step2 = raw17052step1 := by apply Matrix.ext; unfold raw17052step2 raw17052step1; decide +kernel
      have hl : raw17052step1Labels = labelEmbedding9 ∘ raw17052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17052step1 raw17052step1Labels raw17052step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17053step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17053 raw17053Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw17053 raw17053Labels = mixedMoment B raw17053step0 raw17053step0Labels := by
      have ha : raw17053step0 = (fun i j => raw17053 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17053step0 raw17053; decide +kernel
      have hl : raw17053step0Labels = raw17053Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17053 raw17053Labels permutation664 permutation4
    mixedMoment B raw17053step0 raw17053step0Labels = mixedMoment B raw17053step1 raw17053step1Labels := by
      have ha : raw17053step1 = raw17053step0 := by apply Matrix.ext; unfold raw17053step1 raw17053step0; decide +kernel
      have hl : raw17053step0Labels = labelEmbedding7 ∘ raw17053step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17053step0 raw17053step0Labels raw17053step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5382 node5382Labels := by rfl

def raw17054 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17054 raw17054Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw17054 raw17054Labels = mixedMoment B raw17054step0 raw17054step0Labels := by
      have ha : raw17054step0 = (fun i j => raw17054 (permutation450 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17054step0 raw17054; decide +kernel
      have hl : raw17054step0Labels = raw17054Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17054 raw17054Labels permutation450 permutation3
    mixedMoment B raw17054step0 raw17054step0Labels = mixedMoment B raw17054step1 raw17054step1Labels := by
      have ha : raw17054step1 = -raw17054step0 := by apply Matrix.ext; change ∀ i j, raw17054step1 i j = -(raw17054step0 i j); unfold raw17054step1 raw17054step0; decide +kernel
      have hl : raw17054step1Labels = raw17054step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3730 node3730Labels := by rfl

def raw17055 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17055 raw17055Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw17055 raw17055Labels = mixedMoment B raw17055step0 raw17055step0Labels := by
      have ha : raw17055step0 = (fun i j => raw17055 (permutation439 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17055step0 raw17055; decide +kernel
      have hl : raw17055step0Labels = raw17055Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17055 raw17055Labels permutation439 permutation3
    mixedMoment B raw17055step0 raw17055step0Labels = mixedMoment B raw17055step1 raw17055step1Labels := by
      have ha : raw17055step1 = -raw17055step0 := by apply Matrix.ext; change ∀ i j, raw17055step1 i j = -(raw17055step0 i j); unfold raw17055step1 raw17055step0; decide +kernel
      have hl : raw17055step1Labels = raw17055step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3723 node3723Labels := by rfl

def raw17056 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17056 raw17056Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw17056 raw17056Labels = mixedMoment B raw17056step0 raw17056step0Labels := by
      have ha : raw17056step0 = (fun i j => raw17056 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17056step0 raw17056; decide +kernel
      have hl : raw17056step0Labels = raw17056Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17056 raw17056Labels permutation688 permutation6
    mixedMoment B raw17056step0 raw17056step0Labels = mixedMoment B raw17056step1 raw17056step1Labels := by
      have ha : raw17056step1 = -raw17056step0 := by apply Matrix.ext; change ∀ i j, raw17056step1 i j = -(raw17056step0 i j); unfold raw17056step1 raw17056step0; decide +kernel
      have hl : raw17056step1Labels = raw17056step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw17057 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17057 raw17057Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw17057 raw17057Labels = mixedMoment B raw17057step0 raw17057step0Labels := by
      have ha : raw17057step0 = (fun i j => raw17057 (permutation438 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17057step0 raw17057; decide +kernel
      have hl : raw17057step0Labels = raw17057Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17057 raw17057Labels permutation438 permutation3
    mixedMoment B raw17057step0 raw17057step0Labels = mixedMoment B raw17057step1 raw17057step1Labels := by
      have ha : raw17057step1 = -raw17057step0 := by apply Matrix.ext; change ∀ i j, raw17057step1 i j = -(raw17057step0 i j); unfold raw17057step1 raw17057step0; decide +kernel
      have hl : raw17057step1Labels = raw17057step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3724 node3724Labels := by rfl

def raw17058 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw17058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17058 raw17058Labels = mixedMoment B node3727 node3727Labels := by
  calc
    mixedMoment B raw17058 raw17058Labels = mixedMoment B raw17058step0 raw17058step0Labels := by
      have ha : raw17058step0 = (fun i j => raw17058 (permutation436 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17058step0 raw17058; decide +kernel
      have hl : raw17058step0Labels = raw17058Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17058 raw17058Labels permutation436 permutation3
    mixedMoment B raw17058step0 raw17058step0Labels = mixedMoment B raw17058step1 raw17058step1Labels := by
      have ha : raw17058step1 = -raw17058step0 := by apply Matrix.ext; change ∀ i j, raw17058step1 i j = -(raw17058step0 i j); unfold raw17058step1 raw17058step0; decide +kernel
      have hl : raw17058step1Labels = raw17058step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3727 node3727Labels := by rfl

def raw17059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17059 raw17059Labels = mixedMoment B node3826 node3826Labels := by
  calc
    mixedMoment B raw17059 raw17059Labels = mixedMoment B raw17059step0 raw17059step0Labels := by
      have ha : raw17059step0 = (fun i j => raw17059 (permutation409 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17059step0 raw17059; decide +kernel
      have hl : raw17059step0Labels = raw17059Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17059 raw17059Labels permutation409 permutation3
    _ = mixedMoment B node3826 node3826Labels := by rfl

def raw17060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17060 raw17060Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw17060 raw17060Labels = mixedMoment B raw17060step0 raw17060step0Labels := by
      have ha : raw17060step0 = (fun i j => raw17060 (permutation455 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17060step0 raw17060; decide +kernel
      have hl : raw17060step0Labels = raw17060Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17060 raw17060Labels permutation455 permutation3
    mixedMoment B raw17060step0 raw17060step0Labels = mixedMoment B raw17060step1 raw17060step1Labels := by
      have ha : raw17060step1 = -raw17060step0 := by apply Matrix.ext; change ∀ i j, raw17060step1 i j = -(raw17060step0 i j); unfold raw17060step1 raw17060step0; decide +kernel
      have hl : raw17060step1Labels = raw17060step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3827 node3827Labels := by rfl

def raw17061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw17061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17061step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17061 raw17061Labels = mixedMoment B node3830 node3830Labels := by
  calc
    mixedMoment B raw17061 raw17061Labels = mixedMoment B raw17061step0 raw17061step0Labels := by
      have ha : raw17061step0 = (fun i j => raw17061 (permutation453 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17061step0 raw17061; decide +kernel
      have hl : raw17061step0Labels = raw17061Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17061 raw17061Labels permutation453 permutation3
    mixedMoment B raw17061step0 raw17061step0Labels = mixedMoment B raw17061step1 raw17061step1Labels := by
      have ha : raw17061step1 = -raw17061step0 := by apply Matrix.ext; change ∀ i j, raw17061step1 i j = -(raw17061step0 i j); unfold raw17061step1 raw17061step0; decide +kernel
      have hl : raw17061step1Labels = raw17061step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3830 node3830Labels := by rfl

def raw17062 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17062 raw17062Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw17062 raw17062Labels = mixedMoment B raw17062step0 raw17062step0Labels := by
      have hz : ∀ j, raw17062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17062step0 = (fun i j => raw17062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17062step0 raw17062; decide +kernel
      have hl : raw17062step0Labels = raw17062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17062 raw17062Labels permutation346 hz
    mixedMoment B raw17062step0 raw17062step0Labels = mixedMoment B raw17062step1 raw17062step1Labels := by
      have ha : raw17062step1 = (fun i j => raw17062step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17062step1 raw17062step0; decide +kernel
      have hl : raw17062step1Labels = raw17062step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17062step0 raw17062step0Labels permutation32 permutation6
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw17063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17063 raw17063Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw17063 raw17063Labels = mixedMoment B raw17063step0 raw17063step0Labels := by
      have hz : ∀ j, raw17063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17063step0 = (fun i j => raw17063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17063step0 raw17063; decide +kernel
      have hl : raw17063step0Labels = raw17063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17063 raw17063Labels permutation346 hz
    mixedMoment B raw17063step0 raw17063step0Labels = mixedMoment B raw17063step1 raw17063step1Labels := by
      have ha : raw17063step1 = (fun i j => raw17063step0 (permutation81 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17063step1 raw17063step0; decide +kernel
      have hl : raw17063step1Labels = raw17063step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17063step0 raw17063step0Labels permutation81 permutation3
    mixedMoment B raw17063step1 raw17063step1Labels = mixedMoment B raw17063step2 raw17063step2Labels := by
      have ha : raw17063step2 = -raw17063step1 := by apply Matrix.ext; change ∀ i j, raw17063step2 i j = -(raw17063step1 i j); unfold raw17063step2 raw17063step1; decide +kernel
      have hl : raw17063step2Labels = raw17063step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw17064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17064step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw17064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17064 raw17064Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw17064 raw17064Labels = mixedMoment B raw17064step0 raw17064step0Labels := by
      have hz : ∀ j, raw17064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17064step0 = (fun i j => raw17064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17064step0 raw17064; decide +kernel
      have hl : raw17064step0Labels = raw17064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17064 raw17064Labels permutation346 hz
    mixedMoment B raw17064step0 raw17064step0Labels = mixedMoment B raw17064step1 raw17064step1Labels := by
      have ha : raw17064step1 = (fun i j => raw17064step0 (permutation80 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17064step1 raw17064step0; decide +kernel
      have hl : raw17064step1Labels = raw17064step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17064step0 raw17064step0Labels permutation80 permutation3
    mixedMoment B raw17064step1 raw17064step1Labels = mixedMoment B raw17064step2 raw17064step2Labels := by
      have ha : raw17064step2 = -raw17064step1 := by apply Matrix.ext; change ∀ i j, raw17064step2 i j = -(raw17064step1 i j); unfold raw17064step2 raw17064step1; decide +kernel
      have hl : raw17064step2Labels = raw17064step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw17065 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17065 raw17065Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw17065 raw17065Labels = mixedMoment B raw17065step0 raw17065step0Labels := by
      have ha : raw17065step0 = (fun i j => raw17065 (permutation456 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17065step0 raw17065; decide +kernel
      have hl : raw17065step0Labels = raw17065Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17065 raw17065Labels permutation456 permutation3
    mixedMoment B raw17065step0 raw17065step0Labels = mixedMoment B raw17065step1 raw17065step1Labels := by
      have ha : raw17065step1 = -raw17065step0 := by apply Matrix.ext; change ∀ i j, raw17065step1 i j = -(raw17065step0 i j); unfold raw17065step1 raw17065step0; decide +kernel
      have hl : raw17065step1Labels = raw17065step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw17066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17066 raw17066Labels = mixedMoment B node2098 node2098Labels := by
  calc
    mixedMoment B raw17066 raw17066Labels = mixedMoment B raw17066step0 raw17066step0Labels := by
      have ha : raw17066step0 = (fun i j => raw17066 (permutation450 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17066step0 raw17066; decide +kernel
      have hl : raw17066step0Labels = raw17066Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17066 raw17066Labels permutation450 permutation3
    mixedMoment B raw17066step0 raw17066step0Labels = mixedMoment B raw17066step1 raw17066step1Labels := by
      have ha : raw17066step1 = -raw17066step0 := by apply Matrix.ext; change ∀ i j, raw17066step1 i j = -(raw17066step0 i j); unfold raw17066step1 raw17066step0; decide +kernel
      have hl : raw17066step1Labels = raw17066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2098 node2098Labels := by rfl

def raw17067 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17067 raw17067Labels = mixedMoment B node2085 node2085Labels := by
  calc
    mixedMoment B raw17067 raw17067Labels = mixedMoment B raw17067step0 raw17067step0Labels := by
      have ha : raw17067step0 = (fun i j => raw17067 (permutation439 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17067step0 raw17067; decide +kernel
      have hl : raw17067step0Labels = raw17067Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17067 raw17067Labels permutation439 permutation3
    mixedMoment B raw17067step0 raw17067step0Labels = mixedMoment B raw17067step1 raw17067step1Labels := by
      have ha : raw17067step1 = -raw17067step0 := by apply Matrix.ext; change ∀ i j, raw17067step1 i j = -(raw17067step0 i j); unfold raw17067step1 raw17067step0; decide +kernel
      have hl : raw17067step1Labels = raw17067step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2085 node2085Labels := by rfl

def raw17068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17068 raw17068Labels = mixedMoment B node2086 node2086Labels := by
  calc
    mixedMoment B raw17068 raw17068Labels = mixedMoment B raw17068step0 raw17068step0Labels := by
      have ha : raw17068step0 = (fun i j => raw17068 (permutation438 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17068step0 raw17068; decide +kernel
      have hl : raw17068step0Labels = raw17068Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17068 raw17068Labels permutation438 permutation3
    mixedMoment B raw17068step0 raw17068step0Labels = mixedMoment B raw17068step1 raw17068step1Labels := by
      have ha : raw17068step1 = -raw17068step0 := by apply Matrix.ext; change ∀ i j, raw17068step1 i j = -(raw17068step0 i j); unfold raw17068step1 raw17068step0; decide +kernel
      have hl : raw17068step1Labels = raw17068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2086 node2086Labels := by rfl

def raw17069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw17069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17069 raw17069Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw17069 raw17069Labels = mixedMoment B raw17069step0 raw17069step0Labels := by
      have ha : raw17069step0 = (fun i j => raw17069 (permutation436 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17069step0 raw17069; decide +kernel
      have hl : raw17069step0Labels = raw17069Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17069 raw17069Labels permutation436 permutation3
    mixedMoment B raw17069step0 raw17069step0Labels = mixedMoment B raw17069step1 raw17069step1Labels := by
      have ha : raw17069step1 = -raw17069step0 := by apply Matrix.ext; change ∀ i j, raw17069step1 i j = -(raw17069step0 i j); unfold raw17069step1 raw17069step0; decide +kernel
      have hl : raw17069step1Labels = raw17069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2089 node2089Labels := by rfl

def raw17070 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17070 raw17070Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw17070 raw17070Labels = mixedMoment B raw17070step0 raw17070step0Labels := by
      have ha : raw17070step0 = (fun i j => raw17070 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17070step0 raw17070; decide +kernel
      have hl : raw17070step0Labels = raw17070Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17070 raw17070Labels permutation152 permutation6
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw17071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17071 raw17071Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw17071 raw17071Labels = mixedMoment B raw17071step0 raw17071step0Labels := by
      have ha : raw17071step0 = (fun i j => raw17071 (permutation447 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17071step0 raw17071; decide +kernel
      have hl : raw17071step0Labels = raw17071Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17071 raw17071Labels permutation447 permutation3
    mixedMoment B raw17071step0 raw17071step0Labels = mixedMoment B raw17071step1 raw17071step1Labels := by
      have ha : raw17071step1 = -raw17071step0 := by apply Matrix.ext; change ∀ i j, raw17071step1 i j = -(raw17071step0 i j); unfold raw17071step1 raw17071step0; decide +kernel
      have hl : raw17071step1Labels = raw17071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw17072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17072 raw17072Labels = mixedMoment B node3870 node3870Labels := by
  calc
    mixedMoment B raw17072 raw17072Labels = mixedMoment B raw17072step0 raw17072step0Labels := by
      have ha : raw17072step0 = (fun i j => raw17072 (permutation422 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17072step0 raw17072; decide +kernel
      have hl : raw17072step0Labels = raw17072Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17072 raw17072Labels permutation422 permutation3
    _ = mixedMoment B node3870 node3870Labels := by rfl

def raw17073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17073 raw17073Labels = mixedMoment B node3971 node3971Labels := by
  calc
    mixedMoment B raw17073 raw17073Labels = mixedMoment B raw17073step0 raw17073step0Labels := by
      have ha : raw17073step0 = (fun i j => raw17073 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17073step0 raw17073; decide +kernel
      have hl : raw17073step0Labels = raw17073Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17073 raw17073Labels permutation152 permutation6
    _ = mixedMoment B node3971 node3971Labels := by rfl

def raw17074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17074 raw17074Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw17074 raw17074Labels = mixedMoment B raw17074step0 raw17074step0Labels := by
      have ha : raw17074step0 = (fun i j => raw17074 (permutation443 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17074step0 raw17074; decide +kernel
      have hl : raw17074step0Labels = raw17074Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17074 raw17074Labels permutation443 permutation3
    mixedMoment B raw17074step0 raw17074step0Labels = mixedMoment B raw17074step1 raw17074step1Labels := by
      have ha : raw17074step1 = -raw17074step0 := by apply Matrix.ext; change ∀ i j, raw17074step1 i j = -(raw17074step0 i j); unfold raw17074step1 raw17074step0; decide +kernel
      have hl : raw17074step1Labels = raw17074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw17075 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17075 raw17075Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw17075 raw17075Labels = mixedMoment B raw17075step0 raw17075step0Labels := by
      have ha : raw17075step0 = (fun i j => raw17075 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17075step0 raw17075; decide +kernel
      have hl : raw17075step0Labels = raw17075Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17075 raw17075Labels permutation152 permutation6
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw17076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17076 raw17076Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw17076 raw17076Labels = mixedMoment B raw17076step0 raw17076step0Labels := by
      have ha : raw17076step0 = (fun i j => raw17076 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17076step0 raw17076; decide +kernel
      have hl : raw17076step0Labels = raw17076Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17076 raw17076Labels permutation688 permutation6
    mixedMoment B raw17076step0 raw17076step0Labels = mixedMoment B raw17076step1 raw17076step1Labels := by
      have ha : raw17076step1 = -raw17076step0 := by apply Matrix.ext; change ∀ i j, raw17076step1 i j = -(raw17076step0 i j); unfold raw17076step1 raw17076step0; decide +kernel
      have hl : raw17076step1Labels = raw17076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw17077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17077 raw17077Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw17077 raw17077Labels = mixedMoment B raw17077step0 raw17077step0Labels := by
      have ha : raw17077step0 = (fun i j => raw17077 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17077step0 raw17077; decide +kernel
      have hl : raw17077step0Labels = raw17077Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17077 raw17077Labels permutation688 permutation6
    mixedMoment B raw17077step0 raw17077step0Labels = mixedMoment B raw17077step1 raw17077step1Labels := by
      have ha : raw17077step1 = -raw17077step0 := by apply Matrix.ext; change ∀ i j, raw17077step1 i j = -(raw17077step0 i j); unfold raw17077step1 raw17077step0; decide +kernel
      have hl : raw17077step1Labels = raw17077step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw17078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17078 raw17078Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw17078 raw17078Labels = mixedMoment B raw17078step0 raw17078step0Labels := by
      have ha : raw17078step0 = (fun i j => raw17078 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17078step0 raw17078; decide +kernel
      have hl : raw17078step0Labels = raw17078Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17078 raw17078Labels permutation688 permutation6
    mixedMoment B raw17078step0 raw17078step0Labels = mixedMoment B raw17078step1 raw17078step1Labels := by
      have ha : raw17078step1 = -raw17078step0 := by apply Matrix.ext; change ∀ i j, raw17078step1 i j = -(raw17078step0 i j); unfold raw17078step1 raw17078step0; decide +kernel
      have hl : raw17078step1Labels = raw17078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw17079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17079 raw17079Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw17079 raw17079Labels = mixedMoment B raw17079step0 raw17079step0Labels := by
      have ha : raw17079step0 = (fun i j => raw17079 (permutation448 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17079step0 raw17079; decide +kernel
      have hl : raw17079step0Labels = raw17079Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17079 raw17079Labels permutation448 permutation3
    mixedMoment B raw17079step0 raw17079step0Labels = mixedMoment B raw17079step1 raw17079step1Labels := by
      have ha : raw17079step1 = -raw17079step0 := by apply Matrix.ext; change ∀ i j, raw17079step1 i j = -(raw17079step0 i j); unfold raw17079step1 raw17079step0; decide +kernel
      have hl : raw17079step1Labels = raw17079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3866 node3866Labels := by rfl

def raw17080 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17080step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17080 raw17080Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw17080 raw17080Labels = mixedMoment B raw17080step0 raw17080step0Labels := by
      have ha : raw17080step0 = (fun i j => raw17080 (permutation203 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17080step0 raw17080; decide +kernel
      have hl : raw17080step0Labels = raw17080Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17080 raw17080Labels permutation203 permutation2
    mixedMoment B raw17080step0 raw17080step0Labels = mixedMoment B raw17080step1 raw17080step1Labels := by
      have ha : raw17080step1 = -raw17080step0 := by apply Matrix.ext; change ∀ i j, raw17080step1 i j = -(raw17080step0 i j); unfold raw17080step1 raw17080step0; decide +kernel
      have hl : raw17080step1Labels = raw17080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3722 node3722Labels := by rfl

def raw17081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17081 raw17081Labels = mixedMoment B node4022 node4022Labels := by
  calc
    mixedMoment B raw17081 raw17081Labels = mixedMoment B raw17081step0 raw17081step0Labels := by
      have ha : raw17081step0 = (fun i j => raw17081 (permutation430 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17081step0 raw17081; decide +kernel
      have hl : raw17081step0Labels = raw17081Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17081 raw17081Labels permutation430 permutation2
    _ = mixedMoment B node4022 node4022Labels := by rfl

def raw17082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17082 raw17082Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw17082 raw17082Labels = mixedMoment B raw17082step0 raw17082step0Labels := by
      have ha : raw17082step0 = (fun i j => raw17082 (permutation434 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17082step0 raw17082; decide +kernel
      have hl : raw17082step0Labels = raw17082Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17082 raw17082Labels permutation434 permutation2
    mixedMoment B raw17082step0 raw17082step0Labels = mixedMoment B raw17082step1 raw17082step1Labels := by
      have ha : raw17082step1 = -raw17082step0 := by apply Matrix.ext; change ∀ i j, raw17082step1 i j = -(raw17082step0 i j); unfold raw17082step1 raw17082step0; decide +kernel
      have hl : raw17082step1Labels = raw17082step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw17083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17083 raw17083Labels = mixedMoment B node3173 node3173Labels := by
  calc
    mixedMoment B raw17083 raw17083Labels = mixedMoment B raw17083step0 raw17083step0Labels := by
      have ha : raw17083step0 = (fun i j => raw17083 (permutation437 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17083step0 raw17083; decide +kernel
      have hl : raw17083step0Labels = raw17083Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17083 raw17083Labels permutation437 permutation2
    mixedMoment B raw17083step0 raw17083step0Labels = mixedMoment B raw17083step1 raw17083step1Labels := by
      have ha : raw17083step1 = -raw17083step0 := by apply Matrix.ext; change ∀ i j, raw17083step1 i j = -(raw17083step0 i j); unfold raw17083step1 raw17083step0; decide +kernel
      have hl : raw17083step1Labels = raw17083step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3173 node3173Labels := by rfl

def raw17084 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17084 raw17084Labels = mixedMoment B node4022 node4022Labels := by
  calc
    mixedMoment B raw17084 raw17084Labels = mixedMoment B raw17084step0 raw17084step0Labels := by
      have ha : raw17084step0 = (fun i j => raw17084 (permutation516 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17084step0 raw17084; decide +kernel
      have hl : raw17084step0Labels = raw17084Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17084 raw17084Labels permutation516 permutation4
    _ = mixedMoment B node4022 node4022Labels := by rfl

def raw17085 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17085 raw17085Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw17085 raw17085Labels = mixedMoment B raw17085step0 raw17085step0Labels := by
      have ha : raw17085step0 = (fun i j => raw17085 (permutation661 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17085step0 raw17085; decide +kernel
      have hl : raw17085step0Labels = raw17085Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17085 raw17085Labels permutation661 permutation4
    _ = mixedMoment B node3722 node3722Labels := by rfl

def raw17086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17086 raw17086Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw17086 raw17086Labels = mixedMoment B raw17086step0 raw17086step0Labels := by
      have hz : ∀ j, raw17086 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17086step0 = (fun i j => raw17086 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17086step0 raw17086; decide +kernel
      have hl : raw17086step0Labels = raw17086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17086 raw17086Labels permutation346 hz
    mixedMoment B raw17086step0 raw17086step0Labels = mixedMoment B raw17086step1 raw17086step1Labels := by
      have ha : raw17086step1 = (fun i j => raw17086step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17086step1 raw17086step0; decide +kernel
      have hl : raw17086step1Labels = raw17086step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17086step0 raw17086step0Labels permutation56 permutation2
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw17087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17087step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17087step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17087 raw17087Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw17087 raw17087Labels = mixedMoment B raw17087step0 raw17087step0Labels := by
      have ha : raw17087step0 = (fun i j => raw17087 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17087step0 raw17087; decide +kernel
      have hl : raw17087step0Labels = raw17087Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17087 raw17087Labels permutation683 permutation3
    mixedMoment B raw17087step0 raw17087step0Labels = mixedMoment B raw17087step1 raw17087step1Labels := by
      have ha : raw17087step1 = -raw17087step0 := by apply Matrix.ext; change ∀ i j, raw17087step1 i j = -(raw17087step0 i j); unfold raw17087step1 raw17087step0; decide +kernel
      have hl : raw17087step1Labels = raw17087step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17087step1 raw17087step1Labels = mixedMoment B raw17087step2 raw17087step2Labels := by
      have ha : raw17087step2 = raw17087step1 := by apply Matrix.ext; unfold raw17087step2 raw17087step1; decide +kernel
      have hl : raw17087step1Labels = labelEmbedding6 ∘ raw17087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17087step1 raw17087step1Labels raw17087step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw17088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17088step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17088step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17088step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17088step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17088 raw17088Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw17088 raw17088Labels = mixedMoment B raw17088step0 raw17088step0Labels := by
      have hz : ∀ j, raw17088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17088step0 = (fun i j => raw17088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17088step0 raw17088; decide +kernel
      have hl : raw17088step0Labels = raw17088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17088 raw17088Labels permutation346 hz
    mixedMoment B raw17088step0 raw17088step0Labels = mixedMoment B raw17088step1 raw17088step1Labels := by
      have ha : raw17088step1 = (fun i j => raw17088step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17088step1 raw17088step0; decide +kernel
      have hl : raw17088step1Labels = raw17088step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17088step0 raw17088step0Labels permutation146 permutation3
    mixedMoment B raw17088step1 raw17088step1Labels = mixedMoment B raw17088step2 raw17088step2Labels := by
      have ha : raw17088step2 = -raw17088step1 := by apply Matrix.ext; change ∀ i j, raw17088step2 i j = -(raw17088step1 i j); unfold raw17088step2 raw17088step1; decide +kernel
      have hl : raw17088step2Labels = raw17088step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17088step2 raw17088step2Labels = mixedMoment B raw17088step3 raw17088step3Labels := by
      have ha : raw17088step3 = raw17088step2 := by apply Matrix.ext; unfold raw17088step3 raw17088step2; decide +kernel
      have hl : raw17088step2Labels = labelEmbedding6 ∘ raw17088step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17088step2 raw17088step2Labels raw17088step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw17089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw17089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17089 raw17089Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw17089 raw17089Labels = mixedMoment B raw17089step0 raw17089step0Labels := by
      have hz : ∀ j, raw17089 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17089step0 = (fun i j => raw17089 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17089step0 raw17089; decide +kernel
      have hl : raw17089step0Labels = raw17089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17089 raw17089Labels permutation520 hz
    mixedMoment B raw17089step0 raw17089step0Labels = mixedMoment B raw17089step1 raw17089step1Labels := by
      have hz : ∀ j, raw17089step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17089step1 = (fun i j => raw17089step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17089step1 raw17089step0; decide +kernel
      have hl : raw17089step1Labels = raw17089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17089step0 raw17089step0Labels permutation80 hz
    mixedMoment B raw17089step1 raw17089step1Labels = mixedMoment B raw17089step2 raw17089step2Labels := by
      have ha : raw17089step2 = (fun i j => raw17089step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17089step2 raw17089step1; decide +kernel
      have hl : raw17089step2Labels = raw17089step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17089step1 raw17089step1Labels permutation30 permutation2
    mixedMoment B raw17089step2 raw17089step2Labels = mixedMoment B raw17089step3 raw17089step3Labels := by
      have ha : raw17089step3 = -raw17089step2 := by apply Matrix.ext; change ∀ i j, raw17089step3 i j = -(raw17089step2 i j); unfold raw17089step3 raw17089step2; decide +kernel
      have hl : raw17089step3Labels = raw17089step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw17090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17090step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17090 raw17090Labels = mixedMoment B node5460 node5460Labels := by
  calc
    mixedMoment B raw17090 raw17090Labels = mixedMoment B raw17090step0 raw17090step0Labels := by
      have ha : raw17090step0 = (fun i j => raw17090 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17090step0 raw17090; decide +kernel
      have hl : raw17090step0Labels = raw17090Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17090 raw17090Labels permutation158 permutation3
    mixedMoment B raw17090step0 raw17090step0Labels = mixedMoment B raw17090step1 raw17090step1Labels := by
      have ha : raw17090step1 = raw17090step0 := by apply Matrix.ext; unfold raw17090step1 raw17090step0; decide +kernel
      have hl : raw17090step0Labels = labelEmbedding6 ∘ raw17090step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17090step0 raw17090step0Labels raw17090step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5460 node5460Labels := by rfl

def raw17091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17091 raw17091Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw17091 raw17091Labels = mixedMoment B raw17091step0 raw17091step0Labels := by
      have ha : raw17091step0 = (fun i j => raw17091 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17091step0 raw17091; decide +kernel
      have hl : raw17091step0Labels = raw17091Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17091 raw17091Labels permutation200 permutation3
    mixedMoment B raw17091step0 raw17091step0Labels = mixedMoment B raw17091step1 raw17091step1Labels := by
      have ha : raw17091step1 = raw17091step0 := by apply Matrix.ext; unfold raw17091step1 raw17091step0; decide +kernel
      have hl : raw17091step0Labels = labelEmbedding6 ∘ raw17091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17091step0 raw17091step0Labels raw17091step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw17092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw17092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17092 raw17092Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw17092 raw17092Labels = mixedMoment B raw17092step0 raw17092step0Labels := by
      have hz : ∀ j, raw17092 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17092step0 = (fun i j => raw17092 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17092step0 raw17092; decide +kernel
      have hl : raw17092step0Labels = raw17092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17092 raw17092Labels permutation520 hz
    mixedMoment B raw17092step0 raw17092step0Labels = mixedMoment B raw17092step1 raw17092step1Labels := by
      have ha : raw17092step1 = (fun i j => raw17092step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17092step1 raw17092step0; decide +kernel
      have hl : raw17092step1Labels = raw17092step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17092step0 raw17092step0Labels permutation34 permutation2
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw17093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17093 raw17093Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw17093 raw17093Labels = mixedMoment B raw17093step0 raw17093step0Labels := by
      have hz : ∀ j, raw17093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17093step0 = (fun i j => raw17093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17093step0 raw17093; decide +kernel
      have hl : raw17093step0Labels = raw17093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17093 raw17093Labels permutation346 hz
    mixedMoment B raw17093step0 raw17093step0Labels = mixedMoment B raw17093step1 raw17093step1Labels := by
      have ha : raw17093step1 = (fun i j => raw17093step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17093step1 raw17093step0; decide +kernel
      have hl : raw17093step1Labels = raw17093step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17093step0 raw17093step0Labels permutation34 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw17094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17094 raw17094Labels = mixedMoment B node5476 node5476Labels := by
  calc
    mixedMoment B raw17094 raw17094Labels = mixedMoment B raw17094step0 raw17094step0Labels := by
      have ha : raw17094step0 = (fun i j => raw17094 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17094step0 raw17094; decide +kernel
      have hl : raw17094step0Labels = raw17094Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17094 raw17094Labels permutation154 permutation2
    _ = mixedMoment B node5476 node5476Labels := by rfl

def raw17095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17095 raw17095Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw17095 raw17095Labels = mixedMoment B raw17095step0 raw17095step0Labels := by
      have hz : ∀ j, raw17095 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17095step0 = (fun i j => raw17095 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17095step0 raw17095; decide +kernel
      have hl : raw17095step0Labels = raw17095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17095 raw17095Labels permutation520 hz
    mixedMoment B raw17095step0 raw17095step0Labels = mixedMoment B raw17095step1 raw17095step1Labels := by
      have hz : ∀ j, raw17095step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17095step1 = (fun i j => raw17095step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17095step1 raw17095step0; decide +kernel
      have hl : raw17095step1Labels = raw17095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17095step0 raw17095step0Labels permutation80 hz
    _ = mixedMoment B node5487 node5487Labels := by rfl

def raw17096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17096step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17096step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17096step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17096step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17096 raw17096Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw17096 raw17096Labels = mixedMoment B raw17096step0 raw17096step0Labels := by
      have hz : ∀ j, raw17096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17096step0 = (fun i j => raw17096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17096step0 raw17096; decide +kernel
      have hl : raw17096step0Labels = raw17096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17096 raw17096Labels permutation346 hz
    mixedMoment B raw17096step0 raw17096step0Labels = mixedMoment B raw17096step1 raw17096step1Labels := by
      have ha : raw17096step1 = (fun i j => raw17096step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17096step1 raw17096step0; decide +kernel
      have hl : raw17096step1Labels = raw17096step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17096step0 raw17096step0Labels permutation126 permutation3
    mixedMoment B raw17096step1 raw17096step1Labels = mixedMoment B raw17096step2 raw17096step2Labels := by
      have ha : raw17096step2 = -raw17096step1 := by apply Matrix.ext; change ∀ i j, raw17096step2 i j = -(raw17096step1 i j); unfold raw17096step2 raw17096step1; decide +kernel
      have hl : raw17096step2Labels = raw17096step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17096step2 raw17096step2Labels = mixedMoment B raw17096step3 raw17096step3Labels := by
      have ha : raw17096step3 = raw17096step2 := by apply Matrix.ext; unfold raw17096step3 raw17096step2; decide +kernel
      have hl : raw17096step2Labels = labelEmbedding6 ∘ raw17096step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17096step2 raw17096step2Labels raw17096step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw17097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17097step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17097step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17097step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17097step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17097 raw17097Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw17097 raw17097Labels = mixedMoment B raw17097step0 raw17097step0Labels := by
      have ha : raw17097step0 = (fun i j => raw17097 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17097step0 raw17097; decide +kernel
      have hl : raw17097step0Labels = raw17097Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17097 raw17097Labels permutation587 permutation3
    mixedMoment B raw17097step0 raw17097step0Labels = mixedMoment B raw17097step1 raw17097step1Labels := by
      have ha : raw17097step1 = -raw17097step0 := by apply Matrix.ext; change ∀ i j, raw17097step1 i j = -(raw17097step0 i j); unfold raw17097step1 raw17097step0; decide +kernel
      have hl : raw17097step1Labels = raw17097step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17097step1 raw17097step1Labels = mixedMoment B raw17097step2 raw17097step2Labels := by
      have ha : raw17097step2 = raw17097step1 := by apply Matrix.ext; unfold raw17097step2 raw17097step1; decide +kernel
      have hl : raw17097step1Labels = labelEmbedding6 ∘ raw17097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17097step1 raw17097step1Labels raw17097step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw17098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17098step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17098step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17098step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17098step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17098step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17098 raw17098Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17098 raw17098Labels = mixedMoment B raw17098step0 raw17098step0Labels := by
      have hz : ∀ j, raw17098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17098step0 = (fun i j => raw17098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17098step0 raw17098; decide +kernel
      have hl : raw17098step0Labels = raw17098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17098 raw17098Labels permutation346 hz
    mixedMoment B raw17098step0 raw17098step0Labels = mixedMoment B raw17098step1 raw17098step1Labels := by
      have ha : raw17098step1 = (fun i j => raw17098step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17098step1 raw17098step0; decide +kernel
      have hl : raw17098step1Labels = raw17098step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17098step0 raw17098step0Labels permutation125 permutation3
    mixedMoment B raw17098step1 raw17098step1Labels = mixedMoment B raw17098step2 raw17098step2Labels := by
      have ha : raw17098step2 = -raw17098step1 := by apply Matrix.ext; change ∀ i j, raw17098step2 i j = -(raw17098step1 i j); unfold raw17098step2 raw17098step1; decide +kernel
      have hl : raw17098step2Labels = raw17098step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17098step2 raw17098step2Labels = mixedMoment B raw17098step3 raw17098step3Labels := by
      have ha : raw17098step3 = raw17098step2 := by apply Matrix.ext; unfold raw17098step3 raw17098step2; decide +kernel
      have hl : raw17098step2Labels = labelEmbedding6 ∘ raw17098step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17098step2 raw17098step2Labels raw17098step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw17099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17099step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17099step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17099step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17099step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17099 raw17099Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw17099 raw17099Labels = mixedMoment B raw17099step0 raw17099step0Labels := by
      have hz : ∀ j, raw17099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17099step0 = (fun i j => raw17099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17099step0 raw17099; decide +kernel
      have hl : raw17099step0Labels = raw17099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17099 raw17099Labels permutation346 hz
    mixedMoment B raw17099step0 raw17099step0Labels = mixedMoment B raw17099step1 raw17099step1Labels := by
      have ha : raw17099step1 = (fun i j => raw17099step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17099step1 raw17099step0; decide +kernel
      have hl : raw17099step1Labels = raw17099step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17099step0 raw17099step0Labels permutation150 permutation3
    mixedMoment B raw17099step1 raw17099step1Labels = mixedMoment B raw17099step2 raw17099step2Labels := by
      have ha : raw17099step2 = -raw17099step1 := by apply Matrix.ext; change ∀ i j, raw17099step2 i j = -(raw17099step1 i j); unfold raw17099step2 raw17099step1; decide +kernel
      have hl : raw17099step2Labels = raw17099step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17099step2 raw17099step2Labels = mixedMoment B raw17099step3 raw17099step3Labels := by
      have ha : raw17099step3 = raw17099step2 := by apply Matrix.ext; unfold raw17099step3 raw17099step2; decide +kernel
      have hl : raw17099step2Labels = labelEmbedding6 ∘ raw17099step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17099step2 raw17099step2Labels raw17099step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw17100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17100step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17100step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17100step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17100step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17100 raw17100Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw17100 raw17100Labels = mixedMoment B raw17100step0 raw17100step0Labels := by
      have ha : raw17100step0 = (fun i j => raw17100 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17100step0 raw17100; decide +kernel
      have hl : raw17100step0Labels = raw17100Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17100 raw17100Labels permutation686 permutation3
    mixedMoment B raw17100step0 raw17100step0Labels = mixedMoment B raw17100step1 raw17100step1Labels := by
      have ha : raw17100step1 = -raw17100step0 := by apply Matrix.ext; change ∀ i j, raw17100step1 i j = -(raw17100step0 i j); unfold raw17100step1 raw17100step0; decide +kernel
      have hl : raw17100step1Labels = raw17100step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17100step1 raw17100step1Labels = mixedMoment B raw17100step2 raw17100step2Labels := by
      have ha : raw17100step2 = raw17100step1 := by apply Matrix.ext; unfold raw17100step2 raw17100step1; decide +kernel
      have hl : raw17100step1Labels = labelEmbedding6 ∘ raw17100step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17100step1 raw17100step1Labels raw17100step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw17101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17101step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17101step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17101step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17101step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17101 raw17101Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw17101 raw17101Labels = mixedMoment B raw17101step0 raw17101step0Labels := by
      have hz : ∀ j, raw17101 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17101step0 = (fun i j => raw17101 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17101step0 raw17101; decide +kernel
      have hl : raw17101step0Labels = raw17101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17101 raw17101Labels permutation346 hz
    mixedMoment B raw17101step0 raw17101step0Labels = mixedMoment B raw17101step1 raw17101step1Labels := by
      have ha : raw17101step1 = (fun i j => raw17101step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17101step1 raw17101step0; decide +kernel
      have hl : raw17101step1Labels = raw17101step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17101step0 raw17101step0Labels permutation149 permutation3
    mixedMoment B raw17101step1 raw17101step1Labels = mixedMoment B raw17101step2 raw17101step2Labels := by
      have ha : raw17101step2 = -raw17101step1 := by apply Matrix.ext; change ∀ i j, raw17101step2 i j = -(raw17101step1 i j); unfold raw17101step2 raw17101step1; decide +kernel
      have hl : raw17101step2Labels = raw17101step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17101step2 raw17101step2Labels = mixedMoment B raw17101step3 raw17101step3Labels := by
      have ha : raw17101step3 = raw17101step2 := by apply Matrix.ext; unfold raw17101step3 raw17101step2; decide +kernel
      have hl : raw17101step2Labels = labelEmbedding6 ∘ raw17101step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17101step2 raw17101step2Labels raw17101step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw17102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw17102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw17102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1]]
def raw17102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17102step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17102step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17102step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17102step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17102step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17102 raw17102Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw17102 raw17102Labels = mixedMoment B raw17102step0 raw17102step0Labels := by
      have hz : ∀ j, raw17102 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17102step0 = (fun i j => raw17102 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17102step0 raw17102; decide +kernel
      have hl : raw17102step0Labels = raw17102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17102 raw17102Labels permutation520 hz
    mixedMoment B raw17102step0 raw17102step0Labels = mixedMoment B raw17102step1 raw17102step1Labels := by
      have hz : ∀ j, raw17102step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17102step1 = (fun i j => raw17102step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17102step1 raw17102step0; decide +kernel
      have hl : raw17102step1Labels = raw17102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17102step0 raw17102step0Labels permutation80 hz
    mixedMoment B raw17102step1 raw17102step1Labels = mixedMoment B raw17102step2 raw17102step2Labels := by
      have ha : raw17102step2 = (fun i j => raw17102step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17102step2 raw17102step1; decide +kernel
      have hl : raw17102step2Labels = raw17102step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17102step1 raw17102step1Labels permutation31 permutation3
    mixedMoment B raw17102step2 raw17102step2Labels = mixedMoment B raw17102step3 raw17102step3Labels := by
      have ha : raw17102step3 = -raw17102step2 := by apply Matrix.ext; change ∀ i j, raw17102step3 i j = -(raw17102step2 i j); unfold raw17102step3 raw17102step2; decide +kernel
      have hl : raw17102step3Labels = raw17102step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17102step3 raw17102step3Labels = mixedMoment B raw17102step4 raw17102step4Labels := by
      have ha : raw17102step4 = raw17102step3 := by apply Matrix.ext; unfold raw17102step4 raw17102step3; decide +kernel
      have hl : raw17102step3Labels = labelEmbedding6 ∘ raw17102step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17102step3 raw17102step3Labels raw17102step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw17103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17103 raw17103Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw17103 raw17103Labels = mixedMoment B raw17103step0 raw17103step0Labels := by
      have hz : ∀ j, raw17103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17103step0 = (fun i j => raw17103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17103step0 raw17103; decide +kernel
      have hl : raw17103step0Labels = raw17103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17103 raw17103Labels permutation346 hz
    mixedMoment B raw17103step0 raw17103step0Labels = mixedMoment B raw17103step1 raw17103step1Labels := by
      have ha : raw17103step1 = (fun i j => raw17103step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17103step1 raw17103step0; decide +kernel
      have hl : raw17103step1Labels = raw17103step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17103step0 raw17103step0Labels permutation150 permutation3
    mixedMoment B raw17103step1 raw17103step1Labels = mixedMoment B raw17103step2 raw17103step2Labels := by
      have ha : raw17103step2 = -raw17103step1 := by apply Matrix.ext; change ∀ i j, raw17103step2 i j = -(raw17103step1 i j); unfold raw17103step2 raw17103step1; decide +kernel
      have hl : raw17103step2Labels = raw17103step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw17104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17104 raw17104Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw17104 raw17104Labels = mixedMoment B raw17104step0 raw17104step0Labels := by
      have ha : raw17104step0 = (fun i j => raw17104 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17104step0 raw17104; decide +kernel
      have hl : raw17104step0Labels = raw17104Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17104 raw17104Labels permutation683 permutation3
    mixedMoment B raw17104step0 raw17104step0Labels = mixedMoment B raw17104step1 raw17104step1Labels := by
      have ha : raw17104step1 = -raw17104step0 := by apply Matrix.ext; change ∀ i j, raw17104step1 i j = -(raw17104step0 i j); unfold raw17104step1 raw17104step0; decide +kernel
      have hl : raw17104step1Labels = raw17104step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw17105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17105 raw17105Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw17105 raw17105Labels = mixedMoment B raw17105step0 raw17105step0Labels := by
      have hz : ∀ j, raw17105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17105step0 = (fun i j => raw17105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17105step0 raw17105; decide +kernel
      have hl : raw17105step0Labels = raw17105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17105 raw17105Labels permutation346 hz
    mixedMoment B raw17105step0 raw17105step0Labels = mixedMoment B raw17105step1 raw17105step1Labels := by
      have ha : raw17105step1 = (fun i j => raw17105step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17105step1 raw17105step0; decide +kernel
      have hl : raw17105step1Labels = raw17105step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17105step0 raw17105step0Labels permutation146 permutation3
    mixedMoment B raw17105step1 raw17105step1Labels = mixedMoment B raw17105step2 raw17105step2Labels := by
      have ha : raw17105step2 = -raw17105step1 := by apply Matrix.ext; change ∀ i j, raw17105step2 i j = -(raw17105step1 i j); unfold raw17105step2 raw17105step1; decide +kernel
      have hl : raw17105step2Labels = raw17105step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw17106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw17106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17106step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw17106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17106step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw17106step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17106 raw17106Labels = mixedMoment B node4018 node4018Labels := by
  calc
    mixedMoment B raw17106 raw17106Labels = mixedMoment B raw17106step0 raw17106step0Labels := by
      have hz : ∀ j, raw17106 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17106step0 = (fun i j => raw17106 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17106step0 raw17106; decide +kernel
      have hl : raw17106step0Labels = raw17106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17106 raw17106Labels permutation520 hz
    mixedMoment B raw17106step0 raw17106step0Labels = mixedMoment B raw17106step1 raw17106step1Labels := by
      have hz : ∀ j, raw17106step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17106step1 = (fun i j => raw17106step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17106step1 raw17106step0; decide +kernel
      have hl : raw17106step1Labels = raw17106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17106step0 raw17106step0Labels permutation80 hz
    mixedMoment B raw17106step1 raw17106step1Labels = mixedMoment B raw17106step2 raw17106step2Labels := by
      have ha : raw17106step2 = (fun i j => raw17106step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17106step2 raw17106step1; decide +kernel
      have hl : raw17106step2Labels = raw17106step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17106step1 raw17106step1Labels permutation30 permutation3
    mixedMoment B raw17106step2 raw17106step2Labels = mixedMoment B raw17106step3 raw17106step3Labels := by
      have ha : raw17106step3 = -raw17106step2 := by apply Matrix.ext; change ∀ i j, raw17106step3 i j = -(raw17106step2 i j); unfold raw17106step3 raw17106step2; decide +kernel
      have hl : raw17106step3Labels = raw17106step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4018 node4018Labels := by rfl

def raw17107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17107 raw17107Labels = mixedMoment B node3921 node3921Labels := by
  calc
    mixedMoment B raw17107 raw17107Labels = mixedMoment B raw17107step0 raw17107step0Labels := by
      have ha : raw17107step0 = (fun i j => raw17107 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17107step0 raw17107; decide +kernel
      have hl : raw17107step0Labels = raw17107Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17107 raw17107Labels permutation158 permutation3
    _ = mixedMoment B node3921 node3921Labels := by rfl

def raw17108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17108 raw17108Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw17108 raw17108Labels = mixedMoment B raw17108step0 raw17108step0Labels := by
      have ha : raw17108step0 = (fun i j => raw17108 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17108step0 raw17108; decide +kernel
      have hl : raw17108step0Labels = raw17108Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17108 raw17108Labels permutation200 permutation3
    _ = mixedMoment B node3945 node3945Labels := by rfl

def raw17109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw17109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17109 raw17109Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw17109 raw17109Labels = mixedMoment B raw17109step0 raw17109step0Labels := by
      have hz : ∀ j, raw17109 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17109step0 = (fun i j => raw17109 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17109step0 raw17109; decide +kernel
      have hl : raw17109step0Labels = raw17109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17109 raw17109Labels permutation520 hz
    mixedMoment B raw17109step0 raw17109step0Labels = mixedMoment B raw17109step1 raw17109step1Labels := by
      have ha : raw17109step1 = (fun i j => raw17109step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17109step1 raw17109step0; decide +kernel
      have hl : raw17109step1Labels = raw17109step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17109step0 raw17109step0Labels permutation145 permutation3
    mixedMoment B raw17109step1 raw17109step1Labels = mixedMoment B raw17109step2 raw17109step2Labels := by
      have ha : raw17109step2 = -raw17109step1 := by apply Matrix.ext; change ∀ i j, raw17109step2 i j = -(raw17109step1 i j); unfold raw17109step2 raw17109step1; decide +kernel
      have hl : raw17109step2Labels = raw17109step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw17110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17110 raw17110Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw17110 raw17110Labels = mixedMoment B raw17110step0 raw17110step0Labels := by
      have hz : ∀ j, raw17110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17110step0 = (fun i j => raw17110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17110step0 raw17110; decide +kernel
      have hl : raw17110step0Labels = raw17110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17110 raw17110Labels permutation346 hz
    mixedMoment B raw17110step0 raw17110step0Labels = mixedMoment B raw17110step1 raw17110step1Labels := by
      have ha : raw17110step1 = (fun i j => raw17110step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17110step1 raw17110step0; decide +kernel
      have hl : raw17110step1Labels = raw17110step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17110step0 raw17110step0Labels permutation32 permutation3
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw17111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17111 raw17111Labels = mixedMoment B node3965 node3965Labels := by
  calc
    mixedMoment B raw17111 raw17111Labels = mixedMoment B raw17111step0 raw17111step0Labels := by
      have ha : raw17111step0 = (fun i j => raw17111 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17111step0 raw17111; decide +kernel
      have hl : raw17111step0Labels = raw17111Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17111 raw17111Labels permutation176 permutation3
    _ = mixedMoment B node3965 node3965Labels := by rfl

def raw17112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17112step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw17112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17112 raw17112Labels = mixedMoment B node4000 node4000Labels := by
  calc
    mixedMoment B raw17112 raw17112Labels = mixedMoment B raw17112step0 raw17112step0Labels := by
      have hz : ∀ j, raw17112 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17112step0 = (fun i j => raw17112 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17112step0 raw17112; decide +kernel
      have hl : raw17112step0Labels = raw17112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17112 raw17112Labels permutation520 hz
    mixedMoment B raw17112step0 raw17112step0Labels = mixedMoment B raw17112step1 raw17112step1Labels := by
      have hz : ∀ j, raw17112step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17112step1 = (fun i j => raw17112step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17112step1 raw17112step0; decide +kernel
      have hl : raw17112step1Labels = raw17112step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17112step0 raw17112step0Labels permutation80 hz
    mixedMoment B raw17112step1 raw17112step1Labels = mixedMoment B raw17112step2 raw17112step2Labels := by
      have ha : raw17112step2 = (fun i j => raw17112step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17112step2 raw17112step1; decide +kernel
      have hl : raw17112step2Labels = raw17112step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17112step1 raw17112step1Labels permutation8 permutation3
    _ = mixedMoment B node4000 node4000Labels := by rfl

def raw17113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17113step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17113 raw17113Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw17113 raw17113Labels = mixedMoment B raw17113step0 raw17113step0Labels := by
      have hz : ∀ j, raw17113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17113step0 = (fun i j => raw17113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17113step0 raw17113; decide +kernel
      have hl : raw17113step0Labels = raw17113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17113 raw17113Labels permutation346 hz
    mixedMoment B raw17113step0 raw17113step0Labels = mixedMoment B raw17113step1 raw17113step1Labels := by
      have ha : raw17113step1 = (fun i j => raw17113step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17113step1 raw17113step0; decide +kernel
      have hl : raw17113step1Labels = raw17113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17113step0 raw17113step0Labels permutation126 permutation3
    mixedMoment B raw17113step1 raw17113step1Labels = mixedMoment B raw17113step2 raw17113step2Labels := by
      have ha : raw17113step2 = -raw17113step1 := by apply Matrix.ext; change ∀ i j, raw17113step2 i j = -(raw17113step1 i j); unfold raw17113step2 raw17113step1; decide +kernel
      have hl : raw17113step2Labels = raw17113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw17114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17114 raw17114Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw17114 raw17114Labels = mixedMoment B raw17114step0 raw17114step0Labels := by
      have ha : raw17114step0 = (fun i j => raw17114 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17114step0 raw17114; decide +kernel
      have hl : raw17114step0Labels = raw17114Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17114 raw17114Labels permutation587 permutation3
    mixedMoment B raw17114step0 raw17114step0Labels = mixedMoment B raw17114step1 raw17114step1Labels := by
      have ha : raw17114step1 = -raw17114step0 := by apply Matrix.ext; change ∀ i j, raw17114step1 i j = -(raw17114step0 i j); unfold raw17114step1 raw17114step0; decide +kernel
      have hl : raw17114step1Labels = raw17114step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw17115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17115 raw17115Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw17115 raw17115Labels = mixedMoment B raw17115step0 raw17115step0Labels := by
      have hz : ∀ j, raw17115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17115step0 = (fun i j => raw17115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17115step0 raw17115; decide +kernel
      have hl : raw17115step0Labels = raw17115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17115 raw17115Labels permutation346 hz
    mixedMoment B raw17115step0 raw17115step0Labels = mixedMoment B raw17115step1 raw17115step1Labels := by
      have ha : raw17115step1 = (fun i j => raw17115step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17115step1 raw17115step0; decide +kernel
      have hl : raw17115step1Labels = raw17115step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17115step0 raw17115step0Labels permutation125 permutation3
    mixedMoment B raw17115step1 raw17115step1Labels = mixedMoment B raw17115step2 raw17115step2Labels := by
      have ha : raw17115step2 = -raw17115step1 := by apply Matrix.ext; change ∀ i j, raw17115step2 i j = -(raw17115step1 i j); unfold raw17115step2 raw17115step1; decide +kernel
      have hl : raw17115step2Labels = raw17115step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw17116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17116 raw17116Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw17116 raw17116Labels = mixedMoment B raw17116step0 raw17116step0Labels := by
      have hz : ∀ j, raw17116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17116step0 = (fun i j => raw17116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17116step0 raw17116; decide +kernel
      have hl : raw17116step0Labels = raw17116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17116 raw17116Labels permutation346 hz
    mixedMoment B raw17116step0 raw17116step0Labels = mixedMoment B raw17116step1 raw17116step1Labels := by
      have ha : raw17116step1 = (fun i j => raw17116step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17116step1 raw17116step0; decide +kernel
      have hl : raw17116step1Labels = raw17116step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17116step0 raw17116step0Labels permutation150 permutation3
    mixedMoment B raw17116step1 raw17116step1Labels = mixedMoment B raw17116step2 raw17116step2Labels := by
      have ha : raw17116step2 = -raw17116step1 := by apply Matrix.ext; change ∀ i j, raw17116step2 i j = -(raw17116step1 i j); unfold raw17116step2 raw17116step1; decide +kernel
      have hl : raw17116step2Labels = raw17116step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw17117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17117 raw17117Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw17117 raw17117Labels = mixedMoment B raw17117step0 raw17117step0Labels := by
      have ha : raw17117step0 = (fun i j => raw17117 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17117step0 raw17117; decide +kernel
      have hl : raw17117step0Labels = raw17117Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17117 raw17117Labels permutation686 permutation3
    mixedMoment B raw17117step0 raw17117step0Labels = mixedMoment B raw17117step1 raw17117step1Labels := by
      have ha : raw17117step1 = -raw17117step0 := by apply Matrix.ext; change ∀ i j, raw17117step1 i j = -(raw17117step0 i j); unfold raw17117step1 raw17117step0; decide +kernel
      have hl : raw17117step1Labels = raw17117step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw17118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17118 raw17118Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw17118 raw17118Labels = mixedMoment B raw17118step0 raw17118step0Labels := by
      have hz : ∀ j, raw17118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17118step0 = (fun i j => raw17118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17118step0 raw17118; decide +kernel
      have hl : raw17118step0Labels = raw17118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17118 raw17118Labels permutation346 hz
    mixedMoment B raw17118step0 raw17118step0Labels = mixedMoment B raw17118step1 raw17118step1Labels := by
      have ha : raw17118step1 = (fun i j => raw17118step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17118step1 raw17118step0; decide +kernel
      have hl : raw17118step1Labels = raw17118step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17118step0 raw17118step0Labels permutation149 permutation3
    mixedMoment B raw17118step1 raw17118step1Labels = mixedMoment B raw17118step2 raw17118step2Labels := by
      have ha : raw17118step2 = -raw17118step1 := by apply Matrix.ext; change ∀ i j, raw17118step2 i j = -(raw17118step1 i j); unfold raw17118step2 raw17118step1; decide +kernel
      have hl : raw17118step2Labels = raw17118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw17119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw17119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw17119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1]]
def raw17119step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17119step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17119 raw17119Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw17119 raw17119Labels = mixedMoment B raw17119step0 raw17119step0Labels := by
      have hz : ∀ j, raw17119 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17119step0 = (fun i j => raw17119 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17119step0 raw17119; decide +kernel
      have hl : raw17119step0Labels = raw17119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17119 raw17119Labels permutation520 hz
    mixedMoment B raw17119step0 raw17119step0Labels = mixedMoment B raw17119step1 raw17119step1Labels := by
      have hz : ∀ j, raw17119step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17119step1 = (fun i j => raw17119step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17119step1 raw17119step0; decide +kernel
      have hl : raw17119step1Labels = raw17119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17119step0 raw17119step0Labels permutation80 hz
    mixedMoment B raw17119step1 raw17119step1Labels = mixedMoment B raw17119step2 raw17119step2Labels := by
      have ha : raw17119step2 = (fun i j => raw17119step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17119step2 raw17119step1; decide +kernel
      have hl : raw17119step2Labels = raw17119step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17119step1 raw17119step1Labels permutation31 permutation3
    mixedMoment B raw17119step2 raw17119step2Labels = mixedMoment B raw17119step3 raw17119step3Labels := by
      have ha : raw17119step3 = -raw17119step2 := by apply Matrix.ext; change ∀ i j, raw17119step3 i j = -(raw17119step2 i j); unfold raw17119step3 raw17119step2; decide +kernel
      have hl : raw17119step3Labels = raw17119step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw17120 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17120step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17120step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17120step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17120 raw17120Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw17120 raw17120Labels = mixedMoment B raw17120step0 raw17120step0Labels := by
      have hz : ∀ j, raw17120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17120step0 = (fun i j => raw17120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17120step0 raw17120; decide +kernel
      have hl : raw17120step0Labels = raw17120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17120 raw17120Labels permutation434 hz
    mixedMoment B raw17120step0 raw17120step0Labels = mixedMoment B raw17120step1 raw17120step1Labels := by
      have hz : ∀ j, raw17120step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17120step1 = (fun i j => raw17120step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17120step1 raw17120step0; decide +kernel
      have hl : raw17120step1Labels = raw17120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17120step0 raw17120step0Labels permutation80 hz
    mixedMoment B raw17120step1 raw17120step1Labels = mixedMoment B raw17120step2 raw17120step2Labels := by
      have ha : raw17120step2 = (fun i j => raw17120step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17120step2 raw17120step1; decide +kernel
      have hl : raw17120step2Labels = raw17120step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17120step1 raw17120step1Labels permutation8 permutation7
    mixedMoment B raw17120step2 raw17120step2Labels = mixedMoment B raw17120step3 raw17120step3Labels := by
      have ha : raw17120step3 = raw17120step2 := by apply Matrix.ext; unfold raw17120step3 raw17120step2; decide +kernel
      have hl : raw17120step2Labels = labelEmbedding10 ∘ raw17120step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17120step2 raw17120step2Labels raw17120step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw17121 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17121step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17121 raw17121Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw17121 raw17121Labels = mixedMoment B raw17121step0 raw17121step0Labels := by
      have hz : ∀ j, raw17121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17121step0 = (fun i j => raw17121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17121step0 raw17121; decide +kernel
      have hl : raw17121step0Labels = raw17121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17121 raw17121Labels permutation346 hz
    mixedMoment B raw17121step0 raw17121step0Labels = mixedMoment B raw17121step1 raw17121step1Labels := by
      have ha : raw17121step1 = (fun i j => raw17121step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17121step1 raw17121step0; decide +kernel
      have hl : raw17121step1Labels = raw17121step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17121step0 raw17121step0Labels permutation39 permutation2
    mixedMoment B raw17121step1 raw17121step1Labels = mixedMoment B raw17121step2 raw17121step2Labels := by
      have ha : raw17121step2 = -raw17121step1 := by apply Matrix.ext; change ∀ i j, raw17121step2 i j = -(raw17121step1 i j); unfold raw17121step2 raw17121step1; decide +kernel
      have hl : raw17121step2Labels = raw17121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw17122 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17122step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17122 raw17122Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw17122 raw17122Labels = mixedMoment B raw17122step0 raw17122step0Labels := by
      have hz : ∀ j, raw17122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17122step0 = (fun i j => raw17122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17122step0 raw17122; decide +kernel
      have hl : raw17122step0Labels = raw17122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17122 raw17122Labels permutation346 hz
    mixedMoment B raw17122step0 raw17122step0Labels = mixedMoment B raw17122step1 raw17122step1Labels := by
      have ha : raw17122step1 = (fun i j => raw17122step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17122step1 raw17122step0; decide +kernel
      have hl : raw17122step1Labels = raw17122step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17122step0 raw17122step0Labels permutation149 permutation2
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw17123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17123step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17123 raw17123Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw17123 raw17123Labels = mixedMoment B raw17123step0 raw17123step0Labels := by
      have ha : raw17123step0 = (fun i j => raw17123 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17123step0 raw17123; decide +kernel
      have hl : raw17123step0Labels = raw17123Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17123 raw17123Labels permutation152 permutation6
    mixedMoment B raw17123step0 raw17123step0Labels = mixedMoment B raw17123step1 raw17123step1Labels := by
      have ha : raw17123step1 = raw17123step0 := by apply Matrix.ext; unfold raw17123step1 raw17123step0; decide +kernel
      have hl : raw17123step0Labels = labelEmbedding9 ∘ raw17123step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17123step0 raw17123step0Labels raw17123step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw17124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17124step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17124step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17124 raw17124Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw17124 raw17124Labels = mixedMoment B raw17124step0 raw17124step0Labels := by
      have ha : raw17124step0 = (fun i j => raw17124 (permutation439 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17124step0 raw17124; decide +kernel
      have hl : raw17124step0Labels = raw17124Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17124 raw17124Labels permutation439 permutation3
    mixedMoment B raw17124step0 raw17124step0Labels = mixedMoment B raw17124step1 raw17124step1Labels := by
      have ha : raw17124step1 = -raw17124step0 := by apply Matrix.ext; change ∀ i j, raw17124step1 i j = -(raw17124step0 i j); unfold raw17124step1 raw17124step0; decide +kernel
      have hl : raw17124step1Labels = raw17124step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17124step1 raw17124step1Labels = mixedMoment B raw17124step2 raw17124step2Labels := by
      have ha : raw17124step2 = raw17124step1 := by apply Matrix.ext; unfold raw17124step2 raw17124step1; decide +kernel
      have hl : raw17124step1Labels = labelEmbedding6 ∘ raw17124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17124step1 raw17124step1Labels raw17124step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw17125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2]]
def raw17125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17125step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17125step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17125step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17125 raw17125Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw17125 raw17125Labels = mixedMoment B raw17125step0 raw17125step0Labels := by
      have hz : ∀ j, raw17125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17125step0 = (fun i j => raw17125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17125step0 raw17125; decide +kernel
      have hl : raw17125step0Labels = raw17125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17125 raw17125Labels permutation434 hz
    mixedMoment B raw17125step0 raw17125step0Labels = mixedMoment B raw17125step1 raw17125step1Labels := by
      have hz : ∀ j, raw17125step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17125step1 = (fun i j => raw17125step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17125step1 raw17125step0; decide +kernel
      have hl : raw17125step1Labels = raw17125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17125step0 raw17125step0Labels permutation80 hz
    mixedMoment B raw17125step1 raw17125step1Labels = mixedMoment B raw17125step2 raw17125step2Labels := by
      have ha : raw17125step2 = (fun i j => raw17125step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17125step2 raw17125step1; decide +kernel
      have hl : raw17125step2Labels = raw17125step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17125step1 raw17125step1Labels permutation8 permutation6
    mixedMoment B raw17125step2 raw17125step2Labels = mixedMoment B raw17125step3 raw17125step3Labels := by
      have ha : raw17125step3 = raw17125step2 := by apply Matrix.ext; unfold raw17125step3 raw17125step2; decide +kernel
      have hl : raw17125step2Labels = labelEmbedding9 ∘ raw17125step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17125step2 raw17125step2Labels raw17125step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5487 node5487Labels := by rfl

def raw17126 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![0, -2, 2]]
def raw17126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17126step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17126step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17126step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17126step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17126step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17126step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17126 raw17126Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw17126 raw17126Labels = mixedMoment B raw17126step0 raw17126step0Labels := by
      have hz : ∀ j, raw17126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17126step0 = (fun i j => raw17126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17126step0 raw17126; decide +kernel
      have hl : raw17126step0Labels = raw17126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17126 raw17126Labels permutation434 hz
    mixedMoment B raw17126step0 raw17126step0Labels = mixedMoment B raw17126step1 raw17126step1Labels := by
      have hz : ∀ j, raw17126step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17126step1 = (fun i j => raw17126step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17126step1 raw17126step0; decide +kernel
      have hl : raw17126step1Labels = raw17126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17126step0 raw17126step0Labels permutation80 hz
    mixedMoment B raw17126step1 raw17126step1Labels = mixedMoment B raw17126step2 raw17126step2Labels := by
      have ha : raw17126step2 = (fun i j => raw17126step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17126step2 raw17126step1; decide +kernel
      have hl : raw17126step2Labels = raw17126step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17126step1 raw17126step1Labels permutation31 permutation6
    mixedMoment B raw17126step2 raw17126step2Labels = mixedMoment B raw17126step3 raw17126step3Labels := by
      have ha : raw17126step3 = -raw17126step2 := by apply Matrix.ext; change ∀ i j, raw17126step3 i j = -(raw17126step2 i j); unfold raw17126step3 raw17126step2; decide +kernel
      have hl : raw17126step3Labels = raw17126step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17126step3 raw17126step3Labels = mixedMoment B raw17126step4 raw17126step4Labels := by
      have ha : raw17126step4 = raw17126step3 := by apply Matrix.ext; unfold raw17126step4 raw17126step3; decide +kernel
      have hl : raw17126step3Labels = labelEmbedding9 ∘ raw17126step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17126step3 raw17126step3Labels raw17126step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw17127 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17127step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17127 raw17127Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw17127 raw17127Labels = mixedMoment B raw17127step0 raw17127step0Labels := by
      have hz : ∀ j, raw17127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17127step0 = (fun i j => raw17127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17127step0 raw17127; decide +kernel
      have hl : raw17127step0Labels = raw17127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17127 raw17127Labels permutation346 hz
    mixedMoment B raw17127step0 raw17127step0Labels = mixedMoment B raw17127step1 raw17127step1Labels := by
      have ha : raw17127step1 = (fun i j => raw17127step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17127step1 raw17127step0; decide +kernel
      have hl : raw17127step1Labels = raw17127step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17127step0 raw17127step0Labels permutation145 permutation4
    mixedMoment B raw17127step1 raw17127step1Labels = mixedMoment B raw17127step2 raw17127step2Labels := by
      have ha : raw17127step2 = raw17127step1 := by apply Matrix.ext; unfold raw17127step2 raw17127step1; decide +kernel
      have hl : raw17127step1Labels = labelEmbedding7 ∘ raw17127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17127step1 raw17127step1Labels raw17127step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw17128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17128step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17128 raw17128Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw17128 raw17128Labels = mixedMoment B raw17128step0 raw17128step0Labels := by
      have ha : raw17128step0 = (fun i j => raw17128 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17128step0 raw17128; decide +kernel
      have hl : raw17128step0Labels = raw17128Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17128 raw17128Labels permutation182 permutation3
    mixedMoment B raw17128step0 raw17128step0Labels = mixedMoment B raw17128step1 raw17128step1Labels := by
      have ha : raw17128step1 = raw17128step0 := by apply Matrix.ext; unfold raw17128step1 raw17128step0; decide +kernel
      have hl : raw17128step0Labels = labelEmbedding6 ∘ raw17128step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17128step0 raw17128step0Labels raw17128step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw17129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17129step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17129step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17129 raw17129Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17129 raw17129Labels = mixedMoment B raw17129step0 raw17129step0Labels := by
      have ha : raw17129step0 = (fun i j => raw17129 (permutation675 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17129step0 raw17129; decide +kernel
      have hl : raw17129step0Labels = raw17129Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17129 raw17129Labels permutation675 permutation5
    mixedMoment B raw17129step0 raw17129step0Labels = mixedMoment B raw17129step1 raw17129step1Labels := by
      have ha : raw17129step1 = raw17129step0 := by apply Matrix.ext; unfold raw17129step1 raw17129step0; decide +kernel
      have hl : raw17129step0Labels = labelEmbedding8 ∘ raw17129step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17129step0 raw17129step0Labels raw17129step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw17130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17130step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17130 raw17130Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17130 raw17130Labels = mixedMoment B raw17130step0 raw17130step0Labels := by
      have ha : raw17130step0 = (fun i j => raw17130 (permutation673 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17130step0 raw17130; decide +kernel
      have hl : raw17130step0Labels = raw17130Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17130 raw17130Labels permutation673 permutation5
    mixedMoment B raw17130step0 raw17130step0Labels = mixedMoment B raw17130step1 raw17130step1Labels := by
      have ha : raw17130step1 = raw17130step0 := by apply Matrix.ext; unfold raw17130step1 raw17130step0; decide +kernel
      have hl : raw17130step0Labels = labelEmbedding8 ∘ raw17130step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17130step0 raw17130step0Labels raw17130step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw17131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw17131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17131step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17131step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17131 raw17131Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw17131 raw17131Labels = mixedMoment B raw17131step0 raw17131step0Labels := by
      have hz : ∀ j, raw17131 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17131step0 = (fun i j => raw17131 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17131step0 raw17131; decide +kernel
      have hl : raw17131step0Labels = raw17131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17131 raw17131Labels permutation520 hz
    mixedMoment B raw17131step0 raw17131step0Labels = mixedMoment B raw17131step1 raw17131step1Labels := by
      have ha : raw17131step1 = (fun i j => raw17131step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17131step1 raw17131step0; decide +kernel
      have hl : raw17131step1Labels = raw17131step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17131step0 raw17131step0Labels permutation137 permutation5
    mixedMoment B raw17131step1 raw17131step1Labels = mixedMoment B raw17131step2 raw17131step2Labels := by
      have ha : raw17131step2 = raw17131step1 := by apply Matrix.ext; unfold raw17131step2 raw17131step1; decide +kernel
      have hl : raw17131step1Labels = labelEmbedding8 ∘ raw17131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17131step1 raw17131step1Labels raw17131step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw17132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17132step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17132 raw17132Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw17132 raw17132Labels = mixedMoment B raw17132step0 raw17132step0Labels := by
      have ha : raw17132step0 = (fun i j => raw17132 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17132step0 raw17132; decide +kernel
      have hl : raw17132step0Labels = raw17132Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17132 raw17132Labels permutation158 permutation3
    mixedMoment B raw17132step0 raw17132step0Labels = mixedMoment B raw17132step1 raw17132step1Labels := by
      have ha : raw17132step1 = raw17132step0 := by apply Matrix.ext; unfold raw17132step1 raw17132step0; decide +kernel
      have hl : raw17132step0Labels = labelEmbedding6 ∘ raw17132step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17132step0 raw17132step0Labels raw17132step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw17133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17133step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17133step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17133step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17133step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17133 raw17133Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw17133 raw17133Labels = mixedMoment B raw17133step0 raw17133step0Labels := by
      have ha : raw17133step0 = (fun i j => raw17133 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17133step0 raw17133; decide +kernel
      have hl : raw17133step0Labels = raw17133Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17133 raw17133Labels permutation681 permutation3
    mixedMoment B raw17133step0 raw17133step0Labels = mixedMoment B raw17133step1 raw17133step1Labels := by
      have ha : raw17133step1 = -raw17133step0 := by apply Matrix.ext; change ∀ i j, raw17133step1 i j = -(raw17133step0 i j); unfold raw17133step1 raw17133step0; decide +kernel
      have hl : raw17133step1Labels = raw17133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17133step1 raw17133step1Labels = mixedMoment B raw17133step2 raw17133step2Labels := by
      have ha : raw17133step2 = raw17133step1 := by apply Matrix.ext; unfold raw17133step2 raw17133step1; decide +kernel
      have hl : raw17133step1Labels = labelEmbedding6 ∘ raw17133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17133step1 raw17133step1Labels raw17133step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw17134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17134step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17134step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17134step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17134 raw17134Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17134 raw17134Labels = mixedMoment B raw17134step0 raw17134step0Labels := by
      have ha : raw17134step0 = (fun i j => raw17134 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17134step0 raw17134; decide +kernel
      have hl : raw17134step0Labels = raw17134Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17134 raw17134Labels permutation680 permutation3
    mixedMoment B raw17134step0 raw17134step0Labels = mixedMoment B raw17134step1 raw17134step1Labels := by
      have ha : raw17134step1 = -raw17134step0 := by apply Matrix.ext; change ∀ i j, raw17134step1 i j = -(raw17134step0 i j); unfold raw17134step1 raw17134step0; decide +kernel
      have hl : raw17134step1Labels = raw17134step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17134step1 raw17134step1Labels = mixedMoment B raw17134step2 raw17134step2Labels := by
      have ha : raw17134step2 = raw17134step1 := by apply Matrix.ext; unfold raw17134step2 raw17134step1; decide +kernel
      have hl : raw17134step1Labels = labelEmbedding6 ∘ raw17134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17134step1 raw17134step1Labels raw17134step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw17135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw17135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17135step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17135step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17135step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17135 raw17135Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17135 raw17135Labels = mixedMoment B raw17135step0 raw17135step0Labels := by
      have hz : ∀ j, raw17135 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17135step0 = (fun i j => raw17135 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17135step0 raw17135; decide +kernel
      have hl : raw17135step0Labels = raw17135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17135 raw17135Labels permutation520 hz
    mixedMoment B raw17135step0 raw17135step0Labels = mixedMoment B raw17135step1 raw17135step1Labels := by
      have ha : raw17135step1 = (fun i j => raw17135step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17135step1 raw17135step0; decide +kernel
      have hl : raw17135step1Labels = raw17135step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17135step0 raw17135step0Labels permutation145 permutation3
    mixedMoment B raw17135step1 raw17135step1Labels = mixedMoment B raw17135step2 raw17135step2Labels := by
      have ha : raw17135step2 = -raw17135step1 := by apply Matrix.ext; change ∀ i j, raw17135step2 i j = -(raw17135step1 i j); unfold raw17135step2 raw17135step1; decide +kernel
      have hl : raw17135step2Labels = raw17135step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17135step2 raw17135step2Labels = mixedMoment B raw17135step3 raw17135step3Labels := by
      have ha : raw17135step3 = raw17135step2 := by apply Matrix.ext; unfold raw17135step3 raw17135step2; decide +kernel
      have hl : raw17135step2Labels = labelEmbedding6 ∘ raw17135step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17135step2 raw17135step2Labels raw17135step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw17136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17136 raw17136Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw17136 raw17136Labels = mixedMoment B raw17136step0 raw17136step0Labels := by
      have ha : raw17136step0 = (fun i j => raw17136 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17136step0 raw17136; decide +kernel
      have hl : raw17136step0Labels = raw17136Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17136 raw17136Labels permutation152 permutation3
    mixedMoment B raw17136step0 raw17136step0Labels = mixedMoment B raw17136step1 raw17136step1Labels := by
      have ha : raw17136step1 = raw17136step0 := by apply Matrix.ext; unfold raw17136step1 raw17136step0; decide +kernel
      have hl : raw17136step0Labels = labelEmbedding6 ∘ raw17136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17136step0 raw17136step0Labels raw17136step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw17137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17137step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17137step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17137step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17137step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17137 raw17137Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw17137 raw17137Labels = mixedMoment B raw17137step0 raw17137step0Labels := by
      have ha : raw17137step0 = (fun i j => raw17137 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17137step0 raw17137; decide +kernel
      have hl : raw17137step0Labels = raw17137Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17137 raw17137Labels permutation687 permutation3
    mixedMoment B raw17137step0 raw17137step0Labels = mixedMoment B raw17137step1 raw17137step1Labels := by
      have ha : raw17137step1 = -raw17137step0 := by apply Matrix.ext; change ∀ i j, raw17137step1 i j = -(raw17137step0 i j); unfold raw17137step1 raw17137step0; decide +kernel
      have hl : raw17137step1Labels = raw17137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17137step1 raw17137step1Labels = mixedMoment B raw17137step2 raw17137step2Labels := by
      have ha : raw17137step2 = raw17137step1 := by apply Matrix.ext; unfold raw17137step2 raw17137step1; decide +kernel
      have hl : raw17137step1Labels = labelEmbedding6 ∘ raw17137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17137step1 raw17137step1Labels raw17137step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw17138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17138step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17138step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17138step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17138step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17138 raw17138Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17138 raw17138Labels = mixedMoment B raw17138step0 raw17138step0Labels := by
      have ha : raw17138step0 = (fun i j => raw17138 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17138step0 raw17138; decide +kernel
      have hl : raw17138step0Labels = raw17138Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17138 raw17138Labels permutation686 permutation3
    mixedMoment B raw17138step0 raw17138step0Labels = mixedMoment B raw17138step1 raw17138step1Labels := by
      have ha : raw17138step1 = -raw17138step0 := by apply Matrix.ext; change ∀ i j, raw17138step1 i j = -(raw17138step0 i j); unfold raw17138step1 raw17138step0; decide +kernel
      have hl : raw17138step1Labels = raw17138step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17138step1 raw17138step1Labels = mixedMoment B raw17138step2 raw17138step2Labels := by
      have ha : raw17138step2 = raw17138step1 := by apply Matrix.ext; unfold raw17138step2 raw17138step1; decide +kernel
      have hl : raw17138step1Labels = labelEmbedding6 ∘ raw17138step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17138step1 raw17138step1Labels raw17138step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw17139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw17139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17139step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17139step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17139step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17139step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17139 raw17139Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17139 raw17139Labels = mixedMoment B raw17139step0 raw17139step0Labels := by
      have hz : ∀ j, raw17139 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17139step0 = (fun i j => raw17139 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17139step0 raw17139; decide +kernel
      have hl : raw17139step0Labels = raw17139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17139 raw17139Labels permutation520 hz
    mixedMoment B raw17139step0 raw17139step0Labels = mixedMoment B raw17139step1 raw17139step1Labels := by
      have ha : raw17139step1 = (fun i j => raw17139step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17139step1 raw17139step0; decide +kernel
      have hl : raw17139step1Labels = raw17139step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17139step0 raw17139step0Labels permutation151 permutation3
    mixedMoment B raw17139step1 raw17139step1Labels = mixedMoment B raw17139step2 raw17139step2Labels := by
      have ha : raw17139step2 = -raw17139step1 := by apply Matrix.ext; change ∀ i j, raw17139step2 i j = -(raw17139step1 i j); unfold raw17139step2 raw17139step1; decide +kernel
      have hl : raw17139step2Labels = raw17139step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17139step2 raw17139step2Labels = mixedMoment B raw17139step3 raw17139step3Labels := by
      have ha : raw17139step3 = raw17139step2 := by apply Matrix.ext; unfold raw17139step3 raw17139step2; decide +kernel
      have hl : raw17139step2Labels = labelEmbedding6 ∘ raw17139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17139step2 raw17139step2Labels raw17139step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw17140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw17140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw17140step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw17140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17140 raw17140Labels = mixedMoment B node5126 node5126Labels := by
  calc
    mixedMoment B raw17140 raw17140Labels = mixedMoment B raw17140step0 raw17140step0Labels := by
      have ha : raw17140step0 = (fun i j => raw17140 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17140step0 raw17140; decide +kernel
      have hl : raw17140step0Labels = raw17140Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17140 raw17140Labels permutation152 permutation3
    mixedMoment B raw17140step0 raw17140step0Labels = mixedMoment B raw17140step1 raw17140step1Labels := by
      have ha : raw17140step1 = raw17140step0 := by apply Matrix.ext; unfold raw17140step1 raw17140step0; decide +kernel
      have hl : raw17140step0Labels = labelEmbedding6 ∘ raw17140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17140step0 raw17140step0Labels raw17140step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5126 node5126Labels := by rfl

def raw17141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw17141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17141step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17141 raw17141Labels = mixedMoment B node5321 node5321Labels := by
  calc
    mixedMoment B raw17141 raw17141Labels = mixedMoment B raw17141step0 raw17141step0Labels := by
      have ha : raw17141step0 = (fun i j => raw17141 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17141step0 raw17141; decide +kernel
      have hl : raw17141step0Labels = raw17141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17141 raw17141Labels permutation583 permutation3
    mixedMoment B raw17141step0 raw17141step0Labels = mixedMoment B raw17141step1 raw17141step1Labels := by
      have ha : raw17141step1 = -raw17141step0 := by apply Matrix.ext; change ∀ i j, raw17141step1 i j = -(raw17141step0 i j); unfold raw17141step1 raw17141step0; decide +kernel
      have hl : raw17141step1Labels = raw17141step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17141step1 raw17141step1Labels = mixedMoment B raw17141step2 raw17141step2Labels := by
      have ha : raw17141step2 = raw17141step1 := by apply Matrix.ext; unfold raw17141step2 raw17141step1; decide +kernel
      have hl : raw17141step1Labels = labelEmbedding6 ∘ raw17141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17141step1 raw17141step1Labels raw17141step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5321 node5321Labels := by rfl

def raw17142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw17142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17142step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17142step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17142 raw17142Labels = mixedMoment B node5324 node5324Labels := by
  calc
    mixedMoment B raw17142 raw17142Labels = mixedMoment B raw17142step0 raw17142step0Labels := by
      have ha : raw17142step0 = (fun i j => raw17142 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17142step0 raw17142; decide +kernel
      have hl : raw17142step0Labels = raw17142Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17142 raw17142Labels permutation587 permutation3
    mixedMoment B raw17142step0 raw17142step0Labels = mixedMoment B raw17142step1 raw17142step1Labels := by
      have ha : raw17142step1 = -raw17142step0 := by apply Matrix.ext; change ∀ i j, raw17142step1 i j = -(raw17142step0 i j); unfold raw17142step1 raw17142step0; decide +kernel
      have hl : raw17142step1Labels = raw17142step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17142step1 raw17142step1Labels = mixedMoment B raw17142step2 raw17142step2Labels := by
      have ha : raw17142step2 = raw17142step1 := by apply Matrix.ext; unfold raw17142step2 raw17142step1; decide +kernel
      have hl : raw17142step1Labels = labelEmbedding6 ∘ raw17142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17142step1 raw17142step1Labels raw17142step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5324 node5324Labels := by rfl

def raw17143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw17143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17143step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17143step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17143step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17143 raw17143Labels = mixedMoment B node5324 node5324Labels := by
  calc
    mixedMoment B raw17143 raw17143Labels = mixedMoment B raw17143step0 raw17143step0Labels := by
      have ha : raw17143step0 = (fun i j => raw17143 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17143step0 raw17143; decide +kernel
      have hl : raw17143step0Labels = raw17143Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17143 raw17143Labels permutation582 permutation3
    mixedMoment B raw17143step0 raw17143step0Labels = mixedMoment B raw17143step1 raw17143step1Labels := by
      have ha : raw17143step1 = -raw17143step0 := by apply Matrix.ext; change ∀ i j, raw17143step1 i j = -(raw17143step0 i j); unfold raw17143step1 raw17143step0; decide +kernel
      have hl : raw17143step1Labels = raw17143step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17143step1 raw17143step1Labels = mixedMoment B raw17143step2 raw17143step2Labels := by
      have ha : raw17143step2 = raw17143step1 := by apply Matrix.ext; unfold raw17143step2 raw17143step1; decide +kernel
      have hl : raw17143step1Labels = labelEmbedding6 ∘ raw17143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17143step1 raw17143step1Labels raw17143step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5324 node5324Labels := by rfl

def raw17144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw17144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw17144step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17144step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17144step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17144 raw17144Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw17144 raw17144Labels = mixedMoment B raw17144step0 raw17144step0Labels := by
      have ha : raw17144step0 = (fun i j => raw17144 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17144step0 raw17144; decide +kernel
      have hl : raw17144step0Labels = raw17144Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17144 raw17144Labels permutation682 permutation3
    mixedMoment B raw17144step0 raw17144step0Labels = mixedMoment B raw17144step1 raw17144step1Labels := by
      have ha : raw17144step1 = -raw17144step0 := by apply Matrix.ext; change ∀ i j, raw17144step1 i j = -(raw17144step0 i j); unfold raw17144step1 raw17144step0; decide +kernel
      have hl : raw17144step1Labels = raw17144step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17144step1 raw17144step1Labels = mixedMoment B raw17144step2 raw17144step2Labels := by
      have ha : raw17144step2 = raw17144step1 := by apply Matrix.ext; unfold raw17144step2 raw17144step1; decide +kernel
      have hl : raw17144step1Labels = labelEmbedding6 ∘ raw17144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17144step1 raw17144step1Labels raw17144step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

def raw17145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw17145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17145step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17145step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17145step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17145step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17145 raw17145Labels = mixedMoment B node4732 node4732Labels := by
  calc
    mixedMoment B raw17145 raw17145Labels = mixedMoment B raw17145step0 raw17145step0Labels := by
      have ha : raw17145step0 = (fun i j => raw17145 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17145step0 raw17145; decide +kernel
      have hl : raw17145step0Labels = raw17145Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17145 raw17145Labels permutation681 permutation3
    mixedMoment B raw17145step0 raw17145step0Labels = mixedMoment B raw17145step1 raw17145step1Labels := by
      have ha : raw17145step1 = -raw17145step0 := by apply Matrix.ext; change ∀ i j, raw17145step1 i j = -(raw17145step0 i j); unfold raw17145step1 raw17145step0; decide +kernel
      have hl : raw17145step1Labels = raw17145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17145step1 raw17145step1Labels = mixedMoment B raw17145step2 raw17145step2Labels := by
      have ha : raw17145step2 = raw17145step1 := by apply Matrix.ext; unfold raw17145step2 raw17145step1; decide +kernel
      have hl : raw17145step1Labels = labelEmbedding6 ∘ raw17145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17145step1 raw17145step1Labels raw17145step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4732 node4732Labels := by rfl

def raw17146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw17146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17146step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17146step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17146step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17146 raw17146Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw17146 raw17146Labels = mixedMoment B raw17146step0 raw17146step0Labels := by
      have ha : raw17146step0 = (fun i j => raw17146 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17146step0 raw17146; decide +kernel
      have hl : raw17146step0Labels = raw17146Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17146 raw17146Labels permutation686 permutation3
    mixedMoment B raw17146step0 raw17146step0Labels = mixedMoment B raw17146step1 raw17146step1Labels := by
      have ha : raw17146step1 = -raw17146step0 := by apply Matrix.ext; change ∀ i j, raw17146step1 i j = -(raw17146step0 i j); unfold raw17146step1 raw17146step0; decide +kernel
      have hl : raw17146step1Labels = raw17146step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17146step1 raw17146step1Labels = mixedMoment B raw17146step2 raw17146step2Labels := by
      have ha : raw17146step2 = raw17146step1 := by apply Matrix.ext; unfold raw17146step2 raw17146step1; decide +kernel
      have hl : raw17146step1Labels = labelEmbedding6 ∘ raw17146step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17146step1 raw17146step1Labels raw17146step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

def raw17147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw17147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17147step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17147step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17147step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17147 raw17147Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw17147 raw17147Labels = mixedMoment B raw17147step0 raw17147step0Labels := by
      have ha : raw17147step0 = (fun i j => raw17147 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17147step0 raw17147; decide +kernel
      have hl : raw17147step0Labels = raw17147Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17147 raw17147Labels permutation680 permutation3
    mixedMoment B raw17147step0 raw17147step0Labels = mixedMoment B raw17147step1 raw17147step1Labels := by
      have ha : raw17147step1 = -raw17147step0 := by apply Matrix.ext; change ∀ i j, raw17147step1 i j = -(raw17147step0 i j); unfold raw17147step1 raw17147step0; decide +kernel
      have hl : raw17147step1Labels = raw17147step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17147step1 raw17147step1Labels = mixedMoment B raw17147step2 raw17147step2Labels := by
      have ha : raw17147step2 = raw17147step1 := by apply Matrix.ext; unfold raw17147step2 raw17147step1; decide +kernel
      have hl : raw17147step1Labels = labelEmbedding6 ∘ raw17147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17147step1 raw17147step1Labels raw17147step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

def raw17148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw17148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw17148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17148step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17148step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17148step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17148 raw17148Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw17148 raw17148Labels = mixedMoment B raw17148step0 raw17148step0Labels := by
      have hz : ∀ j, raw17148 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17148step0 = (fun i j => raw17148 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17148step0 raw17148; decide +kernel
      have hl : raw17148step0Labels = raw17148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17148 raw17148Labels permutation520 hz
    mixedMoment B raw17148step0 raw17148step0Labels = mixedMoment B raw17148step1 raw17148step1Labels := by
      have ha : raw17148step1 = (fun i j => raw17148step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17148step1 raw17148step0; decide +kernel
      have hl : raw17148step1Labels = raw17148step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17148step0 raw17148step0Labels permutation145 permutation3
    mixedMoment B raw17148step1 raw17148step1Labels = mixedMoment B raw17148step2 raw17148step2Labels := by
      have ha : raw17148step2 = -raw17148step1 := by apply Matrix.ext; change ∀ i j, raw17148step2 i j = -(raw17148step1 i j); unfold raw17148step2 raw17148step1; decide +kernel
      have hl : raw17148step2Labels = raw17148step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17148step2 raw17148step2Labels = mixedMoment B raw17148step3 raw17148step3Labels := by
      have ha : raw17148step3 = raw17148step2 := by apply Matrix.ext; unfold raw17148step3 raw17148step2; decide +kernel
      have hl : raw17148step2Labels = labelEmbedding6 ∘ raw17148step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17148step2 raw17148step2Labels raw17148step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw17149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17149 raw17149Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw17149 raw17149Labels = mixedMoment B raw17149step0 raw17149step0Labels := by
      have ha : raw17149step0 = (fun i j => raw17149 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17149step0 raw17149; decide +kernel
      have hl : raw17149step0Labels = raw17149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17149 raw17149Labels permutation681 permutation3
    mixedMoment B raw17149step0 raw17149step0Labels = mixedMoment B raw17149step1 raw17149step1Labels := by
      have ha : raw17149step1 = -raw17149step0 := by apply Matrix.ext; change ∀ i j, raw17149step1 i j = -(raw17149step0 i j); unfold raw17149step1 raw17149step0; decide +kernel
      have hl : raw17149step1Labels = raw17149step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw17150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17150step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17150step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17150 raw17150Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw17150 raw17150Labels = mixedMoment B raw17150step0 raw17150step0Labels := by
      have ha : raw17150step0 = (fun i j => raw17150 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17150step0 raw17150; decide +kernel
      have hl : raw17150step0Labels = raw17150Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17150 raw17150Labels permutation683 permutation3
    mixedMoment B raw17150step0 raw17150step0Labels = mixedMoment B raw17150step1 raw17150step1Labels := by
      have ha : raw17150step1 = -raw17150step0 := by apply Matrix.ext; change ∀ i j, raw17150step1 i j = -(raw17150step0 i j); unfold raw17150step1 raw17150step0; decide +kernel
      have hl : raw17150step1Labels = raw17150step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw17151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17151 raw17151Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw17151 raw17151Labels = mixedMoment B raw17151step0 raw17151step0Labels := by
      have ha : raw17151step0 = (fun i j => raw17151 (permutation677 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17151step0 raw17151; decide +kernel
      have hl : raw17151step0Labels = raw17151Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17151 raw17151Labels permutation677 permutation3
    mixedMoment B raw17151step0 raw17151step0Labels = mixedMoment B raw17151step1 raw17151step1Labels := by
      have ha : raw17151step1 = -raw17151step0 := by apply Matrix.ext; change ∀ i j, raw17151step1 i j = -(raw17151step0 i j); unfold raw17151step1 raw17151step0; decide +kernel
      have hl : raw17151step1Labels = raw17151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3805 node3805Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
