import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
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

def raw33152 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw33152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33152step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33152 raw33152Labels = mixedMoment B node1876 node1876Labels := by
  calc
    mixedMoment B raw33152 raw33152Labels = mixedMoment B raw33152step0 raw33152step0Labels := by
      have ha : raw33152step0 = (fun i j => raw33152 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33152step0 raw33152; decide +kernel
      have hl : raw33152step0Labels = raw33152Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33152 raw33152Labels permutation164 permutation4
    mixedMoment B raw33152step0 raw33152step0Labels = mixedMoment B raw33152step1 raw33152step1Labels := by
      have ha : raw33152step1 = -raw33152step0 := by apply Matrix.ext; change ∀ i j, raw33152step1 i j = -(raw33152step0 i j); unfold raw33152step1 raw33152step0; decide +kernel
      have hl : raw33152step1Labels = raw33152step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1876 node1876Labels := by rfl

def raw33153 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33153 raw33153Labels = mixedMoment B node1908 node1908Labels := by
  calc
    mixedMoment B raw33153 raw33153Labels = mixedMoment B raw33153step0 raw33153step0Labels := by
      have ha : raw33153step0 = (fun i j => raw33153 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33153step0 raw33153; decide +kernel
      have hl : raw33153step0Labels = raw33153Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33153 raw33153Labels permutation164 permutation4
    mixedMoment B raw33153step0 raw33153step0Labels = mixedMoment B raw33153step1 raw33153step1Labels := by
      have ha : raw33153step1 = -raw33153step0 := by apply Matrix.ext; change ∀ i j, raw33153step1 i j = -(raw33153step0 i j); unfold raw33153step1 raw33153step0; decide +kernel
      have hl : raw33153step1Labels = raw33153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1908 node1908Labels := by rfl

def raw33154 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw33154Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw33154step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33154 raw33154Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw33154 raw33154Labels = mixedMoment B raw33154step0 raw33154step0Labels := by
      have ha : raw33154step0 = (fun i j => raw33154 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33154step0 raw33154; decide +kernel
      have hl : raw33154step0Labels = raw33154Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33154 raw33154Labels permutation164 permutation4
    mixedMoment B raw33154step0 raw33154step0Labels = mixedMoment B raw33154step1 raw33154step1Labels := by
      have ha : raw33154step1 = -raw33154step0 := by apply Matrix.ext; change ∀ i j, raw33154step1 i j = -(raw33154step0 i j); unfold raw33154step1 raw33154step0; decide +kernel
      have hl : raw33154step1Labels = raw33154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1875 node1875Labels := by rfl

def raw33155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33155 raw33155Labels = mixedMoment B node5351 node5351Labels := by
  calc
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw33156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33156 raw33156Labels = mixedMoment B node5400 node5400Labels := by
  calc
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw33157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33157 raw33157Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw33157 raw33157Labels = mixedMoment B raw33157step0 raw33157step0Labels := by
      have hz : ∀ j, raw33157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33157step0 = (fun i j => raw33157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33157step0 raw33157; decide +kernel
      have hl : raw33157step0Labels = raw33157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33157 raw33157Labels permutation434 hz
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw33158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33158 raw33158Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw33158 raw33158Labels = mixedMoment B raw33158step0 raw33158step0Labels := by
      have hz : ∀ j, raw33158 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33158step0 = (fun i j => raw33158 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33158step0 raw33158; decide +kernel
      have hl : raw33158step0Labels = raw33158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33158 raw33158Labels permutation520 hz
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw33159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33159 raw33159Labels = mixedMoment B node5256 node5256Labels := by
  calc
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw33160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33160 raw33160Labels = mixedMoment B node4541 node4541Labels := by
  calc
    mixedMoment B raw33160 raw33160Labels = mixedMoment B raw33160step0 raw33160step0Labels := by
      have ha : raw33160step0 = (fun i j => raw33160 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33160step0 raw33160; decide +kernel
      have hl : raw33160step0Labels = raw33160Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33160 raw33160Labels permutation160 permutation2
    _ = mixedMoment B node4541 node4541Labels := by rfl

def raw33161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33161 raw33161Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw33161 raw33161Labels = mixedMoment B raw33161step0 raw33161step0Labels := by
      have ha : raw33161step0 = (fun i j => raw33161 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33161step0 raw33161; decide +kernel
      have hl : raw33161step0Labels = raw33161Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33161 raw33161Labels permutation160 permutation2
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw33162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33162step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33162 raw33162Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw33162 raw33162Labels = mixedMoment B raw33162step0 raw33162step0Labels := by
      have hz : ∀ j, raw33162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33162step0 = (fun i j => raw33162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33162step0 raw33162; decide +kernel
      have hl : raw33162step0Labels = raw33162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33162 raw33162Labels permutation434 hz
    mixedMoment B raw33162step0 raw33162step0Labels = mixedMoment B raw33162step1 raw33162step1Labels := by
      have ha : raw33162step1 = (fun i j => raw33162step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33162step1 raw33162step0; decide +kernel
      have hl : raw33162step1Labels = raw33162step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33162step0 raw33162step0Labels permutation34 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw33163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33163 raw33163Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw33163 raw33163Labels = mixedMoment B raw33163step0 raw33163step0Labels := by
      have hz : ∀ j, raw33163 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33163step0 = (fun i j => raw33163 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33163step0 raw33163; decide +kernel
      have hl : raw33163step0Labels = raw33163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33163 raw33163Labels permutation520 hz
    mixedMoment B raw33163step0 raw33163step0Labels = mixedMoment B raw33163step1 raw33163step1Labels := by
      have ha : raw33163step1 = (fun i j => raw33163step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33163step1 raw33163step0; decide +kernel
      have hl : raw33163step1Labels = raw33163step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33163step0 raw33163step0Labels permutation34 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw33164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33164 raw33164Labels = mixedMoment B node4529 node4529Labels := by
  calc
    mixedMoment B raw33164 raw33164Labels = mixedMoment B raw33164step0 raw33164step0Labels := by
      have ha : raw33164step0 = (fun i j => raw33164 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33164step0 raw33164; decide +kernel
      have hl : raw33164step0Labels = raw33164Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33164 raw33164Labels permutation154 permutation2
    _ = mixedMoment B node4529 node4529Labels := by rfl

def raw33165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33165 raw33165Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw33165 raw33165Labels = mixedMoment B raw33165step0 raw33165step0Labels := by
      have ha : raw33165step0 = (fun i j => raw33165 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33165step0 raw33165; decide +kernel
      have hl : raw33165step0Labels = raw33165Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33165 raw33165Labels permutation154 permutation2
    _ = mixedMoment B node4931 node4931Labels := by rfl

def raw33166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33166step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33166 raw33166Labels = mixedMoment B node5042 node5042Labels := by
  calc
    mixedMoment B raw33166 raw33166Labels = mixedMoment B raw33166step0 raw33166step0Labels := by
      have ha : raw33166step0 = (fun i j => raw33166 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33166step0 raw33166; decide +kernel
      have hl : raw33166step0Labels = raw33166Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33166 raw33166Labels permutation154 permutation2
    _ = mixedMoment B node5042 node5042Labels := by rfl

def raw33167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33167 raw33167Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw33167 raw33167Labels = mixedMoment B raw33167step0 raw33167step0Labels := by
      have hz : ∀ j, raw33167 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33167step0 = (fun i j => raw33167 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33167step0 raw33167; decide +kernel
      have hl : raw33167step0Labels = raw33167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33167 raw33167Labels permutation520 hz
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw33168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33168 raw33168Labels = mixedMoment B node4529 node4529Labels := by
  calc
    _ = mixedMoment B node4529 node4529Labels := by rfl

def raw33169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33169 raw33169Labels = mixedMoment B node4931 node4931Labels := by
  calc
    _ = mixedMoment B node4931 node4931Labels := by rfl

def raw33170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33170 raw33170Labels = mixedMoment B node5042 node5042Labels := by
  calc
    _ = mixedMoment B node5042 node5042Labels := by rfl

def raw33171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33171 raw33171Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw33171 raw33171Labels = mixedMoment B raw33171step0 raw33171step0Labels := by
      have hz : ∀ j, raw33171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33171step0 = (fun i j => raw33171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33171step0 raw33171; decide +kernel
      have hl : raw33171step0Labels = raw33171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33171 raw33171Labels permutation434 hz
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw33172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33172 raw33172Labels = mixedMoment B node4527 node4527Labels := by
  calc
    _ = mixedMoment B node4527 node4527Labels := by rfl

def raw33173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33173 raw33173Labels = mixedMoment B node4929 node4929Labels := by
  calc
    _ = mixedMoment B node4929 node4929Labels := by rfl

def raw33174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33174 raw33174Labels = mixedMoment B node5041 node5041Labels := by
  calc
    _ = mixedMoment B node5041 node5041Labels := by rfl

def raw33175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33175step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33175 raw33175Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw33175 raw33175Labels = mixedMoment B raw33175step0 raw33175step0Labels := by
      have hz : ∀ j, raw33175 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33175step0 = (fun i j => raw33175 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33175step0 raw33175; decide +kernel
      have hl : raw33175step0Labels = raw33175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33175 raw33175Labels permutation434 hz
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw33176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33176 raw33176Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw33176 raw33176Labels = mixedMoment B raw33176step0 raw33176step0Labels := by
      have hz : ∀ j, raw33176 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33176step0 = (fun i j => raw33176 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33176step0 raw33176; decide +kernel
      have hl : raw33176step0Labels = raw33176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33176 raw33176Labels permutation520 hz
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw33177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33177step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33177step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33177 raw33177Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw33177 raw33177Labels = mixedMoment B raw33177step0 raw33177step0Labels := by
      have ha : raw33177step0 = (fun i j => raw33177 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33177step0 raw33177; decide +kernel
      have hl : raw33177step0Labels = raw33177Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33177 raw33177Labels permutation160 permutation7
    mixedMoment B raw33177step0 raw33177step0Labels = mixedMoment B raw33177step1 raw33177step1Labels := by
      have ha : raw33177step1 = -raw33177step0 := by apply Matrix.ext; change ∀ i j, raw33177step1 i j = -(raw33177step0 i j); unfold raw33177step1 raw33177step0; decide +kernel
      have hl : raw33177step1Labels = raw33177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33177step1 raw33177step1Labels = mixedMoment B raw33177step2 raw33177step2Labels := by
      have ha : raw33177step2 = raw33177step1 := by apply Matrix.ext; unfold raw33177step2 raw33177step1; decide +kernel
      have hl : raw33177step1Labels = labelEmbedding1 ∘ raw33177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33177step1 raw33177step1Labels raw33177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

def raw33178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33178step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33178 raw33178Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw33178 raw33178Labels = mixedMoment B raw33178step0 raw33178step0Labels := by
      have ha : raw33178step0 = (fun i j => raw33178 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33178step0 raw33178; decide +kernel
      have hl : raw33178step0Labels = raw33178Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33178 raw33178Labels permutation160 permutation7
    mixedMoment B raw33178step0 raw33178step0Labels = mixedMoment B raw33178step1 raw33178step1Labels := by
      have ha : raw33178step1 = -raw33178step0 := by apply Matrix.ext; change ∀ i j, raw33178step1 i j = -(raw33178step0 i j); unfold raw33178step1 raw33178step0; decide +kernel
      have hl : raw33178step1Labels = raw33178step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33178step1 raw33178step1Labels = mixedMoment B raw33178step2 raw33178step2Labels := by
      have ha : raw33178step2 = raw33178step1 := by apply Matrix.ext; unfold raw33178step2 raw33178step1; decide +kernel
      have hl : raw33178step1Labels = labelEmbedding1 ∘ raw33178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33178step1 raw33178step1Labels raw33178step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw33179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33179step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33179step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33179 raw33179Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw33179 raw33179Labels = mixedMoment B raw33179step0 raw33179step0Labels := by
      have hz : ∀ j, raw33179 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33179step0 = (fun i j => raw33179 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33179step0 raw33179; decide +kernel
      have hl : raw33179step0Labels = raw33179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33179 raw33179Labels permutation434 hz
    mixedMoment B raw33179step0 raw33179step0Labels = mixedMoment B raw33179step1 raw33179step1Labels := by
      have ha : raw33179step1 = (fun i j => raw33179step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33179step1 raw33179step0; decide +kernel
      have hl : raw33179step1Labels = raw33179step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33179step0 raw33179step0Labels permutation34 permutation7
    mixedMoment B raw33179step1 raw33179step1Labels = mixedMoment B raw33179step2 raw33179step2Labels := by
      have ha : raw33179step2 = -raw33179step1 := by apply Matrix.ext; change ∀ i j, raw33179step2 i j = -(raw33179step1 i j); unfold raw33179step2 raw33179step1; decide +kernel
      have hl : raw33179step2Labels = raw33179step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33179step2 raw33179step2Labels = mixedMoment B raw33179step3 raw33179step3Labels := by
      have ha : raw33179step3 = raw33179step2 := by apply Matrix.ext; unfold raw33179step3 raw33179step2; decide +kernel
      have hl : raw33179step2Labels = labelEmbedding1 ∘ raw33179step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33179step2 raw33179step2Labels raw33179step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw33180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33180step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33180 raw33180Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw33180 raw33180Labels = mixedMoment B raw33180step0 raw33180step0Labels := by
      have hz : ∀ j, raw33180 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33180step0 = (fun i j => raw33180 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33180step0 raw33180; decide +kernel
      have hl : raw33180step0Labels = raw33180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33180 raw33180Labels permutation520 hz
    mixedMoment B raw33180step0 raw33180step0Labels = mixedMoment B raw33180step1 raw33180step1Labels := by
      have ha : raw33180step1 = (fun i j => raw33180step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33180step1 raw33180step0; decide +kernel
      have hl : raw33180step1Labels = raw33180step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33180step0 raw33180step0Labels permutation34 permutation7
    mixedMoment B raw33180step1 raw33180step1Labels = mixedMoment B raw33180step2 raw33180step2Labels := by
      have ha : raw33180step2 = -raw33180step1 := by apply Matrix.ext; change ∀ i j, raw33180step2 i j = -(raw33180step1 i j); unfold raw33180step2 raw33180step1; decide +kernel
      have hl : raw33180step2Labels = raw33180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33180step2 raw33180step2Labels = mixedMoment B raw33180step3 raw33180step3Labels := by
      have ha : raw33180step3 = raw33180step2 := by apply Matrix.ext; unfold raw33180step3 raw33180step2; decide +kernel
      have hl : raw33180step2Labels = labelEmbedding1 ∘ raw33180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33180step2 raw33180step2Labels raw33180step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw33181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw33181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33181 raw33181Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw33181 raw33181Labels = mixedMoment B raw33181step0 raw33181step0Labels := by
      have ha : raw33181step0 = (fun i j => raw33181 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33181step0 raw33181; decide +kernel
      have hl : raw33181step0Labels = raw33181Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33181 raw33181Labels permutation160 permutation7
    mixedMoment B raw33181step0 raw33181step0Labels = mixedMoment B raw33181step1 raw33181step1Labels := by
      have ha : raw33181step1 = -raw33181step0 := by apply Matrix.ext; change ∀ i j, raw33181step1 i j = -(raw33181step0 i j); unfold raw33181step1 raw33181step0; decide +kernel
      have hl : raw33181step1Labels = raw33181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33181step1 raw33181step1Labels = mixedMoment B raw33181step2 raw33181step2Labels := by
      have ha : raw33181step2 = raw33181step1 := by apply Matrix.ext; unfold raw33181step2 raw33181step1; decide +kernel
      have hl : raw33181step1Labels = labelEmbedding1 ∘ raw33181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33181step1 raw33181step1Labels raw33181step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

def raw33182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33182step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33182 raw33182Labels = mixedMoment B node3256 node3256Labels := by
  calc
    mixedMoment B raw33182 raw33182Labels = mixedMoment B raw33182step0 raw33182step0Labels := by
      have ha : raw33182step0 = (fun i j => raw33182 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33182step0 raw33182; decide +kernel
      have hl : raw33182step0Labels = raw33182Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33182 raw33182Labels permutation160 permutation7
    mixedMoment B raw33182step0 raw33182step0Labels = mixedMoment B raw33182step1 raw33182step1Labels := by
      have ha : raw33182step1 = -raw33182step0 := by apply Matrix.ext; change ∀ i j, raw33182step1 i j = -(raw33182step0 i j); unfold raw33182step1 raw33182step0; decide +kernel
      have hl : raw33182step1Labels = raw33182step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33182step1 raw33182step1Labels = mixedMoment B raw33182step2 raw33182step2Labels := by
      have ha : raw33182step2 = raw33182step1 := by apply Matrix.ext; unfold raw33182step2 raw33182step1; decide +kernel
      have hl : raw33182step1Labels = labelEmbedding1 ∘ raw33182step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33182step1 raw33182step1Labels raw33182step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3256 node3256Labels := by rfl

def raw33183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33183 raw33183Labels = mixedMoment B node3404 node3404Labels := by
  calc
    mixedMoment B raw33183 raw33183Labels = mixedMoment B raw33183step0 raw33183step0Labels := by
      have ha : raw33183step0 = (fun i j => raw33183 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33183step0 raw33183; decide +kernel
      have hl : raw33183step0Labels = raw33183Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33183 raw33183Labels permutation160 permutation7
    mixedMoment B raw33183step0 raw33183step0Labels = mixedMoment B raw33183step1 raw33183step1Labels := by
      have ha : raw33183step1 = -raw33183step0 := by apply Matrix.ext; change ∀ i j, raw33183step1 i j = -(raw33183step0 i j); unfold raw33183step1 raw33183step0; decide +kernel
      have hl : raw33183step1Labels = raw33183step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33183step1 raw33183step1Labels = mixedMoment B raw33183step2 raw33183step2Labels := by
      have ha : raw33183step2 = raw33183step1 := by apply Matrix.ext; unfold raw33183step2 raw33183step1; decide +kernel
      have hl : raw33183step1Labels = labelEmbedding1 ∘ raw33183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33183step1 raw33183step1Labels raw33183step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3404 node3404Labels := by rfl

def raw33184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33184step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33184step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33184step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33184 raw33184Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw33184 raw33184Labels = mixedMoment B raw33184step0 raw33184step0Labels := by
      have hz : ∀ j, raw33184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33184step0 = (fun i j => raw33184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33184step0 raw33184; decide +kernel
      have hl : raw33184step0Labels = raw33184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33184 raw33184Labels permutation434 hz
    mixedMoment B raw33184step0 raw33184step0Labels = mixedMoment B raw33184step1 raw33184step1Labels := by
      have ha : raw33184step1 = (fun i j => raw33184step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33184step1 raw33184step0; decide +kernel
      have hl : raw33184step1Labels = raw33184step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33184step0 raw33184step0Labels permutation34 permutation7
    mixedMoment B raw33184step1 raw33184step1Labels = mixedMoment B raw33184step2 raw33184step2Labels := by
      have ha : raw33184step2 = -raw33184step1 := by apply Matrix.ext; change ∀ i j, raw33184step2 i j = -(raw33184step1 i j); unfold raw33184step2 raw33184step1; decide +kernel
      have hl : raw33184step2Labels = raw33184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33184step2 raw33184step2Labels = mixedMoment B raw33184step3 raw33184step3Labels := by
      have ha : raw33184step3 = raw33184step2 := by apply Matrix.ext; unfold raw33184step3 raw33184step2; decide +kernel
      have hl : raw33184step2Labels = labelEmbedding1 ∘ raw33184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33184step2 raw33184step2Labels raw33184step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

def raw33185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33185step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33185step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33185 raw33185Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw33185 raw33185Labels = mixedMoment B raw33185step0 raw33185step0Labels := by
      have hz : ∀ j, raw33185 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33185step0 = (fun i j => raw33185 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33185step0 raw33185; decide +kernel
      have hl : raw33185step0Labels = raw33185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33185 raw33185Labels permutation520 hz
    mixedMoment B raw33185step0 raw33185step0Labels = mixedMoment B raw33185step1 raw33185step1Labels := by
      have ha : raw33185step1 = (fun i j => raw33185step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33185step1 raw33185step0; decide +kernel
      have hl : raw33185step1Labels = raw33185step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33185step0 raw33185step0Labels permutation34 permutation7
    mixedMoment B raw33185step1 raw33185step1Labels = mixedMoment B raw33185step2 raw33185step2Labels := by
      have ha : raw33185step2 = -raw33185step1 := by apply Matrix.ext; change ∀ i j, raw33185step2 i j = -(raw33185step1 i j); unfold raw33185step2 raw33185step1; decide +kernel
      have hl : raw33185step2Labels = raw33185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33185step2 raw33185step2Labels = mixedMoment B raw33185step3 raw33185step3Labels := by
      have ha : raw33185step3 = raw33185step2 := by apply Matrix.ext; unfold raw33185step3 raw33185step2; decide +kernel
      have hl : raw33185step2Labels = labelEmbedding1 ∘ raw33185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33185step2 raw33185step2Labels raw33185step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

def raw33186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw33186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33186step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33186 raw33186Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw33186 raw33186Labels = mixedMoment B raw33186step0 raw33186step0Labels := by
      have ha : raw33186step0 = (fun i j => raw33186 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33186step0 raw33186; decide +kernel
      have hl : raw33186step0Labels = raw33186Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33186 raw33186Labels permutation166 permutation7
    mixedMoment B raw33186step0 raw33186step0Labels = mixedMoment B raw33186step1 raw33186step1Labels := by
      have ha : raw33186step1 = -raw33186step0 := by apply Matrix.ext; change ∀ i j, raw33186step1 i j = -(raw33186step0 i j); unfold raw33186step1 raw33186step0; decide +kernel
      have hl : raw33186step1Labels = raw33186step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33186step1 raw33186step1Labels = mixedMoment B raw33186step2 raw33186step2Labels := by
      have ha : raw33186step2 = raw33186step1 := by apply Matrix.ext; unfold raw33186step2 raw33186step1; decide +kernel
      have hl : raw33186step1Labels = labelEmbedding1 ∘ raw33186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33186step1 raw33186step1Labels raw33186step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3258 node3258Labels := by rfl

def raw33187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw33187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33187 raw33187Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw33187 raw33187Labels = mixedMoment B raw33187step0 raw33187step0Labels := by
      have ha : raw33187step0 = (fun i j => raw33187 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33187step0 raw33187; decide +kernel
      have hl : raw33187step0Labels = raw33187Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33187 raw33187Labels permutation166 permutation7
    mixedMoment B raw33187step0 raw33187step0Labels = mixedMoment B raw33187step1 raw33187step1Labels := by
      have ha : raw33187step1 = -raw33187step0 := by apply Matrix.ext; change ∀ i j, raw33187step1 i j = -(raw33187step0 i j); unfold raw33187step1 raw33187step0; decide +kernel
      have hl : raw33187step1Labels = raw33187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33187step1 raw33187step1Labels = mixedMoment B raw33187step2 raw33187step2Labels := by
      have ha : raw33187step2 = raw33187step1 := by apply Matrix.ext; unfold raw33187step2 raw33187step1; decide +kernel
      have hl : raw33187step1Labels = labelEmbedding1 ∘ raw33187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33187step1 raw33187step1Labels raw33187step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

def raw33188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw33188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33188step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33188 raw33188Labels = mixedMoment B node3462 node3462Labels := by
  calc
    mixedMoment B raw33188 raw33188Labels = mixedMoment B raw33188step0 raw33188step0Labels := by
      have ha : raw33188step0 = (fun i j => raw33188 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33188step0 raw33188; decide +kernel
      have hl : raw33188step0Labels = raw33188Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33188 raw33188Labels permutation166 permutation7
    mixedMoment B raw33188step0 raw33188step0Labels = mixedMoment B raw33188step1 raw33188step1Labels := by
      have ha : raw33188step1 = -raw33188step0 := by apply Matrix.ext; change ∀ i j, raw33188step1 i j = -(raw33188step0 i j); unfold raw33188step1 raw33188step0; decide +kernel
      have hl : raw33188step1Labels = raw33188step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33188step1 raw33188step1Labels = mixedMoment B raw33188step2 raw33188step2Labels := by
      have ha : raw33188step2 = raw33188step1 := by apply Matrix.ext; unfold raw33188step2 raw33188step1; decide +kernel
      have hl : raw33188step1Labels = labelEmbedding1 ∘ raw33188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33188step1 raw33188step1Labels raw33188step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3462 node3462Labels := by rfl

def raw33189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw33189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33189 raw33189Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw33189 raw33189Labels = mixedMoment B raw33189step0 raw33189step0Labels := by
      have hz : ∀ j, raw33189 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33189step0 = (fun i j => raw33189 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33189step0 raw33189; decide +kernel
      have hl : raw33189step0Labels = raw33189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33189 raw33189Labels permutation520 hz
    mixedMoment B raw33189step0 raw33189step0Labels = mixedMoment B raw33189step1 raw33189step1Labels := by
      have ha : raw33189step1 = (fun i j => raw33189step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33189step1 raw33189step0; decide +kernel
      have hl : raw33189step1Labels = raw33189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33189step0 raw33189step0Labels permutation34 permutation7
    mixedMoment B raw33189step1 raw33189step1Labels = mixedMoment B raw33189step2 raw33189step2Labels := by
      have ha : raw33189step2 = -raw33189step1 := by apply Matrix.ext; change ∀ i j, raw33189step2 i j = -(raw33189step1 i j); unfold raw33189step2 raw33189step1; decide +kernel
      have hl : raw33189step2Labels = raw33189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33189step2 raw33189step2Labels = mixedMoment B raw33189step3 raw33189step3Labels := by
      have ha : raw33189step3 = raw33189step2 := by apply Matrix.ext; unfold raw33189step3 raw33189step2; decide +kernel
      have hl : raw33189step2Labels = labelEmbedding1 ∘ raw33189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33189step2 raw33189step2Labels raw33189step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw33190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw33190step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33190step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33190 raw33190Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw33190 raw33190Labels = mixedMoment B raw33190step0 raw33190step0Labels := by
      have ha : raw33190step0 = (fun i j => raw33190 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33190step0 raw33190; decide +kernel
      have hl : raw33190step0Labels = raw33190Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33190 raw33190Labels permutation160 permutation7
    mixedMoment B raw33190step0 raw33190step0Labels = mixedMoment B raw33190step1 raw33190step1Labels := by
      have ha : raw33190step1 = -raw33190step0 := by apply Matrix.ext; change ∀ i j, raw33190step1 i j = -(raw33190step0 i j); unfold raw33190step1 raw33190step0; decide +kernel
      have hl : raw33190step1Labels = raw33190step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33190step1 raw33190step1Labels = mixedMoment B raw33190step2 raw33190step2Labels := by
      have ha : raw33190step2 = raw33190step1 := by apply Matrix.ext; unfold raw33190step2 raw33190step1; decide +kernel
      have hl : raw33190step1Labels = labelEmbedding1 ∘ raw33190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33190step1 raw33190step1Labels raw33190step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3258 node3258Labels := by rfl

def raw33191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw33191step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33191step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33191 raw33191Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw33191 raw33191Labels = mixedMoment B raw33191step0 raw33191step0Labels := by
      have ha : raw33191step0 = (fun i j => raw33191 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33191step0 raw33191; decide +kernel
      have hl : raw33191step0Labels = raw33191Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33191 raw33191Labels permutation160 permutation7
    mixedMoment B raw33191step0 raw33191step0Labels = mixedMoment B raw33191step1 raw33191step1Labels := by
      have ha : raw33191step1 = -raw33191step0 := by apply Matrix.ext; change ∀ i j, raw33191step1 i j = -(raw33191step0 i j); unfold raw33191step1 raw33191step0; decide +kernel
      have hl : raw33191step1Labels = raw33191step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33191step1 raw33191step1Labels = mixedMoment B raw33191step2 raw33191step2Labels := by
      have ha : raw33191step2 = raw33191step1 := by apply Matrix.ext; unfold raw33191step2 raw33191step1; decide +kernel
      have hl : raw33191step1Labels = labelEmbedding1 ∘ raw33191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33191step1 raw33191step1Labels raw33191step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

def raw33192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw33192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33192 raw33192Labels = mixedMoment B node3462 node3462Labels := by
  calc
    mixedMoment B raw33192 raw33192Labels = mixedMoment B raw33192step0 raw33192step0Labels := by
      have ha : raw33192step0 = (fun i j => raw33192 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33192step0 raw33192; decide +kernel
      have hl : raw33192step0Labels = raw33192Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33192 raw33192Labels permutation160 permutation7
    mixedMoment B raw33192step0 raw33192step0Labels = mixedMoment B raw33192step1 raw33192step1Labels := by
      have ha : raw33192step1 = -raw33192step0 := by apply Matrix.ext; change ∀ i j, raw33192step1 i j = -(raw33192step0 i j); unfold raw33192step1 raw33192step0; decide +kernel
      have hl : raw33192step1Labels = raw33192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33192step1 raw33192step1Labels = mixedMoment B raw33192step2 raw33192step2Labels := by
      have ha : raw33192step2 = raw33192step1 := by apply Matrix.ext; unfold raw33192step2 raw33192step1; decide +kernel
      have hl : raw33192step1Labels = labelEmbedding1 ∘ raw33192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33192step1 raw33192step1Labels raw33192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3462 node3462Labels := by rfl

def raw33193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw33193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33193step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33193step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33193 raw33193Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw33193 raw33193Labels = mixedMoment B raw33193step0 raw33193step0Labels := by
      have hz : ∀ j, raw33193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33193step0 = (fun i j => raw33193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33193step0 raw33193; decide +kernel
      have hl : raw33193step0Labels = raw33193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33193 raw33193Labels permutation434 hz
    mixedMoment B raw33193step0 raw33193step0Labels = mixedMoment B raw33193step1 raw33193step1Labels := by
      have ha : raw33193step1 = (fun i j => raw33193step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33193step1 raw33193step0; decide +kernel
      have hl : raw33193step1Labels = raw33193step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33193step0 raw33193step0Labels permutation34 permutation7
    mixedMoment B raw33193step1 raw33193step1Labels = mixedMoment B raw33193step2 raw33193step2Labels := by
      have ha : raw33193step2 = -raw33193step1 := by apply Matrix.ext; change ∀ i j, raw33193step2 i j = -(raw33193step1 i j); unfold raw33193step2 raw33193step1; decide +kernel
      have hl : raw33193step2Labels = raw33193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33193step2 raw33193step2Labels = mixedMoment B raw33193step3 raw33193step3Labels := by
      have ha : raw33193step3 = raw33193step2 := by apply Matrix.ext; unfold raw33193step3 raw33193step2; decide +kernel
      have hl : raw33193step2Labels = labelEmbedding1 ∘ raw33193step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33193step2 raw33193step2Labels raw33193step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw33194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw33194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33194step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33194 raw33194Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw33194 raw33194Labels = mixedMoment B raw33194step0 raw33194step0Labels := by
      have ha : raw33194step0 = (fun i j => raw33194 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33194step0 raw33194; decide +kernel
      have hl : raw33194step0Labels = raw33194Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33194 raw33194Labels permutation160 permutation7
    mixedMoment B raw33194step0 raw33194step0Labels = mixedMoment B raw33194step1 raw33194step1Labels := by
      have ha : raw33194step1 = -raw33194step0 := by apply Matrix.ext; change ∀ i j, raw33194step1 i j = -(raw33194step0 i j); unfold raw33194step1 raw33194step0; decide +kernel
      have hl : raw33194step1Labels = raw33194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33194step1 raw33194step1Labels = mixedMoment B raw33194step2 raw33194step2Labels := by
      have ha : raw33194step2 = raw33194step1 := by apply Matrix.ext; unfold raw33194step2 raw33194step1; decide +kernel
      have hl : raw33194step1Labels = labelEmbedding1 ∘ raw33194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33194step1 raw33194step1Labels raw33194step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3255 node3255Labels := by rfl

def raw33195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw33195step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33195step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33195 raw33195Labels = mixedMoment B node3403 node3403Labels := by
  calc
    mixedMoment B raw33195 raw33195Labels = mixedMoment B raw33195step0 raw33195step0Labels := by
      have ha : raw33195step0 = (fun i j => raw33195 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33195step0 raw33195; decide +kernel
      have hl : raw33195step0Labels = raw33195Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33195 raw33195Labels permutation160 permutation7
    mixedMoment B raw33195step0 raw33195step0Labels = mixedMoment B raw33195step1 raw33195step1Labels := by
      have ha : raw33195step1 = -raw33195step0 := by apply Matrix.ext; change ∀ i j, raw33195step1 i j = -(raw33195step0 i j); unfold raw33195step1 raw33195step0; decide +kernel
      have hl : raw33195step1Labels = raw33195step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33195step1 raw33195step1Labels = mixedMoment B raw33195step2 raw33195step2Labels := by
      have ha : raw33195step2 = raw33195step1 := by apply Matrix.ext; unfold raw33195step2 raw33195step1; decide +kernel
      have hl : raw33195step1Labels = labelEmbedding1 ∘ raw33195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33195step1 raw33195step1Labels raw33195step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3403 node3403Labels := by rfl

def raw33196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw33196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw33196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw33196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33196 raw33196Labels = mixedMoment B node3458 node3458Labels := by
  calc
    mixedMoment B raw33196 raw33196Labels = mixedMoment B raw33196step0 raw33196step0Labels := by
      have ha : raw33196step0 = (fun i j => raw33196 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33196step0 raw33196; decide +kernel
      have hl : raw33196step0Labels = raw33196Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33196 raw33196Labels permutation160 permutation7
    mixedMoment B raw33196step0 raw33196step0Labels = mixedMoment B raw33196step1 raw33196step1Labels := by
      have ha : raw33196step1 = -raw33196step0 := by apply Matrix.ext; change ∀ i j, raw33196step1 i j = -(raw33196step0 i j); unfold raw33196step1 raw33196step0; decide +kernel
      have hl : raw33196step1Labels = raw33196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33196step1 raw33196step1Labels = mixedMoment B raw33196step2 raw33196step2Labels := by
      have ha : raw33196step2 = raw33196step1 := by apply Matrix.ext; unfold raw33196step2 raw33196step1; decide +kernel
      have hl : raw33196step1Labels = labelEmbedding1 ∘ raw33196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33196step1 raw33196step1Labels raw33196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3458 node3458Labels := by rfl

def raw33197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw33197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33197step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33197 raw33197Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw33197 raw33197Labels = mixedMoment B raw33197step0 raw33197step0Labels := by
      have hz : ∀ j, raw33197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33197step0 = (fun i j => raw33197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33197step0 raw33197; decide +kernel
      have hl : raw33197step0Labels = raw33197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33197 raw33197Labels permutation434 hz
    mixedMoment B raw33197step0 raw33197step0Labels = mixedMoment B raw33197step1 raw33197step1Labels := by
      have ha : raw33197step1 = (fun i j => raw33197step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33197step1 raw33197step0; decide +kernel
      have hl : raw33197step1Labels = raw33197step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33197step0 raw33197step0Labels permutation34 permutation7
    mixedMoment B raw33197step1 raw33197step1Labels = mixedMoment B raw33197step2 raw33197step2Labels := by
      have ha : raw33197step2 = -raw33197step1 := by apply Matrix.ext; change ∀ i j, raw33197step2 i j = -(raw33197step1 i j); unfold raw33197step2 raw33197step1; decide +kernel
      have hl : raw33197step2Labels = raw33197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33197step2 raw33197step2Labels = mixedMoment B raw33197step3 raw33197step3Labels := by
      have ha : raw33197step3 = raw33197step2 := by apply Matrix.ext; unfold raw33197step3 raw33197step2; decide +kernel
      have hl : raw33197step2Labels = labelEmbedding1 ∘ raw33197step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33197step2 raw33197step2Labels raw33197step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw33198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw33198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33198step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33198step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33198 raw33198Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw33198 raw33198Labels = mixedMoment B raw33198step0 raw33198step0Labels := by
      have hz : ∀ j, raw33198 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33198step0 = (fun i j => raw33198 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33198step0 raw33198; decide +kernel
      have hl : raw33198step0Labels = raw33198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33198 raw33198Labels permutation520 hz
    mixedMoment B raw33198step0 raw33198step0Labels = mixedMoment B raw33198step1 raw33198step1Labels := by
      have ha : raw33198step1 = (fun i j => raw33198step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33198step1 raw33198step0; decide +kernel
      have hl : raw33198step1Labels = raw33198step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33198step0 raw33198step0Labels permutation34 permutation7
    mixedMoment B raw33198step1 raw33198step1Labels = mixedMoment B raw33198step2 raw33198step2Labels := by
      have ha : raw33198step2 = -raw33198step1 := by apply Matrix.ext; change ∀ i j, raw33198step2 i j = -(raw33198step1 i j); unfold raw33198step2 raw33198step1; decide +kernel
      have hl : raw33198step2Labels = raw33198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33198step2 raw33198step2Labels = mixedMoment B raw33198step3 raw33198step3Labels := by
      have ha : raw33198step3 = raw33198step2 := by apply Matrix.ext; unfold raw33198step3 raw33198step2; decide +kernel
      have hl : raw33198step2Labels = labelEmbedding1 ∘ raw33198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33198step2 raw33198step2Labels raw33198step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw33199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33199step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33199 raw33199Labels = mixedMoment B node4298 node4298Labels := by
  calc
    mixedMoment B raw33199 raw33199Labels = mixedMoment B raw33199step0 raw33199step0Labels := by
      have ha : raw33199step0 = (fun i j => raw33199 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33199step0 raw33199; decide +kernel
      have hl : raw33199step0Labels = raw33199Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33199 raw33199Labels permutation160 permutation3
    mixedMoment B raw33199step0 raw33199step0Labels = mixedMoment B raw33199step1 raw33199step1Labels := by
      have ha : raw33199step1 = raw33199step0 := by apply Matrix.ext; unfold raw33199step1 raw33199step0; decide +kernel
      have hl : raw33199step0Labels = labelEmbedding6 ∘ raw33199step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33199step0 raw33199step0Labels raw33199step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4298 node4298Labels := by rfl

def raw33200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33200step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33200 raw33200Labels = mixedMoment B node4910 node4910Labels := by
  calc
    mixedMoment B raw33200 raw33200Labels = mixedMoment B raw33200step0 raw33200step0Labels := by
      have ha : raw33200step0 = (fun i j => raw33200 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33200step0 raw33200; decide +kernel
      have hl : raw33200step0Labels = raw33200Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33200 raw33200Labels permutation160 permutation3
    mixedMoment B raw33200step0 raw33200step0Labels = mixedMoment B raw33200step1 raw33200step1Labels := by
      have ha : raw33200step1 = raw33200step0 := by apply Matrix.ext; unfold raw33200step1 raw33200step0; decide +kernel
      have hl : raw33200step0Labels = labelEmbedding6 ∘ raw33200step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33200step0 raw33200step0Labels raw33200step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4910 node4910Labels := by rfl

def raw33201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33201step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33201 raw33201Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw33201 raw33201Labels = mixedMoment B raw33201step0 raw33201step0Labels := by
      have ha : raw33201step0 = (fun i j => raw33201 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33201step0 raw33201; decide +kernel
      have hl : raw33201step0Labels = raw33201Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33201 raw33201Labels permutation166 permutation3
    mixedMoment B raw33201step0 raw33201step0Labels = mixedMoment B raw33201step1 raw33201step1Labels := by
      have ha : raw33201step1 = raw33201step0 := by apply Matrix.ext; unfold raw33201step1 raw33201step0; decide +kernel
      have hl : raw33201step0Labels = labelEmbedding6 ∘ raw33201step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33201step0 raw33201step0Labels raw33201step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw33202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33202step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33202 raw33202Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw33202 raw33202Labels = mixedMoment B raw33202step0 raw33202step0Labels := by
      have ha : raw33202step0 = (fun i j => raw33202 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33202step0 raw33202; decide +kernel
      have hl : raw33202step0Labels = raw33202Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33202 raw33202Labels permutation154 permutation3
    mixedMoment B raw33202step0 raw33202step0Labels = mixedMoment B raw33202step1 raw33202step1Labels := by
      have ha : raw33202step1 = raw33202step0 := by apply Matrix.ext; unfold raw33202step1 raw33202step0; decide +kernel
      have hl : raw33202step0Labels = labelEmbedding6 ∘ raw33202step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33202step0 raw33202step0Labels raw33202step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4288 node4288Labels := by rfl

def raw33203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33203step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33203step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33203step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33203 raw33203Labels = mixedMoment B node4903 node4903Labels := by
  calc
    mixedMoment B raw33203 raw33203Labels = mixedMoment B raw33203step0 raw33203step0Labels := by
      have ha : raw33203step0 = (fun i j => raw33203 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33203step0 raw33203; decide +kernel
      have hl : raw33203step0Labels = raw33203Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33203 raw33203Labels permutation154 permutation3
    mixedMoment B raw33203step0 raw33203step0Labels = mixedMoment B raw33203step1 raw33203step1Labels := by
      have ha : raw33203step1 = raw33203step0 := by apply Matrix.ext; unfold raw33203step1 raw33203step0; decide +kernel
      have hl : raw33203step0Labels = labelEmbedding6 ∘ raw33203step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33203step0 raw33203step0Labels raw33203step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4903 node4903Labels := by rfl

def raw33204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33204step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33204step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33204 raw33204Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw33204 raw33204Labels = mixedMoment B raw33204step0 raw33204step0Labels := by
      have ha : raw33204step0 = (fun i j => raw33204 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33204step0 raw33204; decide +kernel
      have hl : raw33204step0Labels = raw33204Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33204 raw33204Labels permutation154 permutation3
    mixedMoment B raw33204step0 raw33204step0Labels = mixedMoment B raw33204step1 raw33204step1Labels := by
      have ha : raw33204step1 = raw33204step0 := by apply Matrix.ext; unfold raw33204step1 raw33204step0; decide +kernel
      have hl : raw33204step0Labels = labelEmbedding6 ∘ raw33204step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33204step0 raw33204step0Labels raw33204step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw33205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33205step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33205step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33205 raw33205Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw33205 raw33205Labels = mixedMoment B raw33205step0 raw33205step0Labels := by
      have ha : raw33205step0 = (fun i j => raw33205 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33205step0 raw33205; decide +kernel
      have hl : raw33205step0Labels = raw33205Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33205 raw33205Labels permutation164 permutation3
    mixedMoment B raw33205step0 raw33205step0Labels = mixedMoment B raw33205step1 raw33205step1Labels := by
      have ha : raw33205step1 = raw33205step0 := by apply Matrix.ext; unfold raw33205step1 raw33205step0; decide +kernel
      have hl : raw33205step0Labels = labelEmbedding6 ∘ raw33205step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33205step0 raw33205step0Labels raw33205step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw33206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33206step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33206 raw33206Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw33206 raw33206Labels = mixedMoment B raw33206step0 raw33206step0Labels := by
      have ha : raw33206step0 = (fun i j => raw33206 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33206step0 raw33206; decide +kernel
      have hl : raw33206step0Labels = raw33206Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33206 raw33206Labels permutation152 permutation3
    mixedMoment B raw33206step0 raw33206step0Labels = mixedMoment B raw33206step1 raw33206step1Labels := by
      have ha : raw33206step1 = raw33206step0 := by apply Matrix.ext; unfold raw33206step1 raw33206step0; decide +kernel
      have hl : raw33206step0Labels = labelEmbedding6 ∘ raw33206step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33206step0 raw33206step0Labels raw33206step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4288 node4288Labels := by rfl

def raw33207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33207step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33207step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33207 raw33207Labels = mixedMoment B node4903 node4903Labels := by
  calc
    mixedMoment B raw33207 raw33207Labels = mixedMoment B raw33207step0 raw33207step0Labels := by
      have ha : raw33207step0 = (fun i j => raw33207 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33207step0 raw33207; decide +kernel
      have hl : raw33207step0Labels = raw33207Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33207 raw33207Labels permutation152 permutation3
    mixedMoment B raw33207step0 raw33207step0Labels = mixedMoment B raw33207step1 raw33207step1Labels := by
      have ha : raw33207step1 = raw33207step0 := by apply Matrix.ext; unfold raw33207step1 raw33207step0; decide +kernel
      have hl : raw33207step0Labels = labelEmbedding6 ∘ raw33207step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33207step0 raw33207step0Labels raw33207step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4903 node4903Labels := by rfl

def raw33208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33208step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33208 raw33208Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw33208 raw33208Labels = mixedMoment B raw33208step0 raw33208step0Labels := by
      have ha : raw33208step0 = (fun i j => raw33208 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33208step0 raw33208; decide +kernel
      have hl : raw33208step0Labels = raw33208Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33208 raw33208Labels permutation152 permutation3
    mixedMoment B raw33208step0 raw33208step0Labels = mixedMoment B raw33208step1 raw33208step1Labels := by
      have ha : raw33208step1 = raw33208step0 := by apply Matrix.ext; unfold raw33208step1 raw33208step0; decide +kernel
      have hl : raw33208step0Labels = labelEmbedding6 ∘ raw33208step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33208step0 raw33208step0Labels raw33208step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw33209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33209step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33209 raw33209Labels = mixedMoment B node4286 node4286Labels := by
  calc
    mixedMoment B raw33209 raw33209Labels = mixedMoment B raw33209step0 raw33209step0Labels := by
      have ha : raw33209step0 = (fun i j => raw33209 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33209step0 raw33209; decide +kernel
      have hl : raw33209step0Labels = raw33209Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33209 raw33209Labels permutation152 permutation3
    mixedMoment B raw33209step0 raw33209step0Labels = mixedMoment B raw33209step1 raw33209step1Labels := by
      have ha : raw33209step1 = raw33209step0 := by apply Matrix.ext; unfold raw33209step1 raw33209step0; decide +kernel
      have hl : raw33209step0Labels = labelEmbedding6 ∘ raw33209step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33209step0 raw33209step0Labels raw33209step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4286 node4286Labels := by rfl

def raw33210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw33210step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw33210step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33210step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw33210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33210 raw33210Labels = mixedMoment B node4755 node4755Labels := by
  calc
    mixedMoment B raw33210 raw33210Labels = mixedMoment B raw33210step0 raw33210step0Labels := by
      have ha : raw33210step0 = (fun i j => raw33210 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33210step0 raw33210; decide +kernel
      have hl : raw33210step0Labels = raw33210Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33210 raw33210Labels permutation664 permutation3
    mixedMoment B raw33210step0 raw33210step0Labels = mixedMoment B raw33210step1 raw33210step1Labels := by
      have ha : raw33210step1 = -raw33210step0 := by apply Matrix.ext; change ∀ i j, raw33210step1 i j = -(raw33210step0 i j); unfold raw33210step1 raw33210step0; decide +kernel
      have hl : raw33210step1Labels = raw33210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33210step1 raw33210step1Labels = mixedMoment B raw33210step2 raw33210step2Labels := by
      have ha : raw33210step2 = raw33210step1 := by apply Matrix.ext; unfold raw33210step2 raw33210step1; decide +kernel
      have hl : raw33210step1Labels = labelEmbedding6 ∘ raw33210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33210step1 raw33210step1Labels raw33210step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4755 node4755Labels := by rfl

def raw33211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw33211step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33211step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33211step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33211step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33211 raw33211Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw33211 raw33211Labels = mixedMoment B raw33211step0 raw33211step0Labels := by
      have ha : raw33211step0 = (fun i j => raw33211 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33211step0 raw33211; decide +kernel
      have hl : raw33211step0Labels = raw33211Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33211 raw33211Labels permutation664 permutation3
    mixedMoment B raw33211step0 raw33211step0Labels = mixedMoment B raw33211step1 raw33211step1Labels := by
      have ha : raw33211step1 = -raw33211step0 := by apply Matrix.ext; change ∀ i j, raw33211step1 i j = -(raw33211step0 i j); unfold raw33211step1 raw33211step0; decide +kernel
      have hl : raw33211step1Labels = raw33211step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33211step1 raw33211step1Labels = mixedMoment B raw33211step2 raw33211step2Labels := by
      have ha : raw33211step2 = raw33211step1 := by apply Matrix.ext; unfold raw33211step2 raw33211step1; decide +kernel
      have hl : raw33211step1Labels = labelEmbedding6 ∘ raw33211step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33211step1 raw33211step1Labels raw33211step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4760 node4760Labels := by rfl

def raw33212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33212step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33212step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33212step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33212step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33212 raw33212Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw33212 raw33212Labels = mixedMoment B raw33212step0 raw33212step0Labels := by
      have ha : raw33212step0 = (fun i j => raw33212 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33212step0 raw33212; decide +kernel
      have hl : raw33212step0Labels = raw33212Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33212 raw33212Labels permutation658 permutation3
    mixedMoment B raw33212step0 raw33212step0Labels = mixedMoment B raw33212step1 raw33212step1Labels := by
      have ha : raw33212step1 = -raw33212step0 := by apply Matrix.ext; change ∀ i j, raw33212step1 i j = -(raw33212step0 i j); unfold raw33212step1 raw33212step0; decide +kernel
      have hl : raw33212step1Labels = raw33212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33212step1 raw33212step1Labels = mixedMoment B raw33212step2 raw33212step2Labels := by
      have ha : raw33212step2 = raw33212step1 := by apply Matrix.ext; unfold raw33212step2 raw33212step1; decide +kernel
      have hl : raw33212step1Labels = labelEmbedding6 ∘ raw33212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33212step1 raw33212step1Labels raw33212step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw33213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33213Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33213 raw33213Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw33213 raw33213Labels = mixedMoment B raw33213step0 raw33213step0Labels := by
      have ha : raw33213step0 = (fun i j => raw33213 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33213step0 raw33213; decide +kernel
      have hl : raw33213step0Labels = raw33213Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33213 raw33213Labels permutation682 permutation3
    mixedMoment B raw33213step0 raw33213step0Labels = mixedMoment B raw33213step1 raw33213step1Labels := by
      have ha : raw33213step1 = -raw33213step0 := by apply Matrix.ext; change ∀ i j, raw33213step1 i j = -(raw33213step0 i j); unfold raw33213step1 raw33213step0; decide +kernel
      have hl : raw33213step1Labels = raw33213step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw33214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33214Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33214step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33214 raw33214Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw33214 raw33214Labels = mixedMoment B raw33214step0 raw33214step0Labels := by
      have hz : ∀ j, raw33214 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33214step0 = (fun i j => raw33214 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33214step0 raw33214; decide +kernel
      have hl : raw33214step0Labels = raw33214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33214 raw33214Labels permutation265 hz
    mixedMoment B raw33214step0 raw33214step0Labels = mixedMoment B raw33214step1 raw33214step1Labels := by
      have ha : raw33214step1 = (fun i j => raw33214step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33214step1 raw33214step0; decide +kernel
      have hl : raw33214step1Labels = raw33214step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33214step0 raw33214step0Labels permutation32 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw33215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33215Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33215 raw33215Labels = mixedMoment B node876 node876Labels := by
  calc
    mixedMoment B raw33215 raw33215Labels = mixedMoment B raw33215step0 raw33215step0Labels := by
      have ha : raw33215step0 = (fun i j => raw33215 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33215step0 raw33215; decide +kernel
      have hl : raw33215step0Labels = raw33215Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33215 raw33215Labels permutation160 permutation3
    _ = mixedMoment B node876 node876Labels := by rfl

def raw33216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33216Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33216 raw33216Labels = mixedMoment B node2303 node2303Labels := by
  calc
    mixedMoment B raw33216 raw33216Labels = mixedMoment B raw33216step0 raw33216step0Labels := by
      have ha : raw33216step0 = (fun i j => raw33216 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33216step0 raw33216; decide +kernel
      have hl : raw33216step0Labels = raw33216Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33216 raw33216Labels permutation160 permutation3
    _ = mixedMoment B node2303 node2303Labels := by rfl

def raw33217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33217Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33217 raw33217Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw33217 raw33217Labels = mixedMoment B raw33217step0 raw33217step0Labels := by
      have ha : raw33217step0 = (fun i j => raw33217 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33217step0 raw33217; decide +kernel
      have hl : raw33217step0Labels = raw33217Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33217 raw33217Labels permutation166 permutation3
    _ = mixedMoment B node2459 node2459Labels := by rfl

def raw33218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33218Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33218 raw33218Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw33218 raw33218Labels = mixedMoment B raw33218step0 raw33218step0Labels := by
      have ha : raw33218step0 = (fun i j => raw33218 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33218step0 raw33218; decide +kernel
      have hl : raw33218step0Labels = raw33218Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33218 raw33218Labels permutation154 permutation3
    _ = mixedMoment B node866 node866Labels := by rfl

def raw33219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33219Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33219 raw33219Labels = mixedMoment B node2296 node2296Labels := by
  calc
    mixedMoment B raw33219 raw33219Labels = mixedMoment B raw33219step0 raw33219step0Labels := by
      have ha : raw33219step0 = (fun i j => raw33219 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33219step0 raw33219; decide +kernel
      have hl : raw33219step0Labels = raw33219Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33219 raw33219Labels permutation154 permutation3
    _ = mixedMoment B node2296 node2296Labels := by rfl

def raw33220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33220Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33220 raw33220Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw33220 raw33220Labels = mixedMoment B raw33220step0 raw33220step0Labels := by
      have ha : raw33220step0 = (fun i j => raw33220 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33220step0 raw33220; decide +kernel
      have hl : raw33220step0Labels = raw33220Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33220 raw33220Labels permutation154 permutation3
    _ = mixedMoment B node2428 node2428Labels := by rfl

def raw33221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33221Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33221 raw33221Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw33221 raw33221Labels = mixedMoment B raw33221step0 raw33221step0Labels := by
      have ha : raw33221step0 = (fun i j => raw33221 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33221step0 raw33221; decide +kernel
      have hl : raw33221step0Labels = raw33221Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33221 raw33221Labels permutation164 permutation3
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw33222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33222Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33222 raw33222Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw33222 raw33222Labels = mixedMoment B raw33222step0 raw33222step0Labels := by
      have ha : raw33222step0 = (fun i j => raw33222 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33222step0 raw33222; decide +kernel
      have hl : raw33222step0Labels = raw33222Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33222 raw33222Labels permutation152 permutation3
    _ = mixedMoment B node866 node866Labels := by rfl

def raw33223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33223Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33223 raw33223Labels = mixedMoment B node2296 node2296Labels := by
  calc
    mixedMoment B raw33223 raw33223Labels = mixedMoment B raw33223step0 raw33223step0Labels := by
      have ha : raw33223step0 = (fun i j => raw33223 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33223step0 raw33223; decide +kernel
      have hl : raw33223step0Labels = raw33223Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33223 raw33223Labels permutation152 permutation3
    _ = mixedMoment B node2296 node2296Labels := by rfl

def raw33224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33224Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33224 raw33224Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw33224 raw33224Labels = mixedMoment B raw33224step0 raw33224step0Labels := by
      have ha : raw33224step0 = (fun i j => raw33224 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33224step0 raw33224; decide +kernel
      have hl : raw33224step0Labels = raw33224Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33224 raw33224Labels permutation152 permutation3
    _ = mixedMoment B node2428 node2428Labels := by rfl

def raw33225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33225Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33225 raw33225Labels = mixedMoment B node864 node864Labels := by
  calc
    mixedMoment B raw33225 raw33225Labels = mixedMoment B raw33225step0 raw33225step0Labels := by
      have ha : raw33225step0 = (fun i j => raw33225 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33225step0 raw33225; decide +kernel
      have hl : raw33225step0Labels = raw33225Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33225 raw33225Labels permutation152 permutation3
    _ = mixedMoment B node864 node864Labels := by rfl

def raw33226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33226Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw33226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw33226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33226 raw33226Labels = mixedMoment B node1954 node1954Labels := by
  calc
    mixedMoment B raw33226 raw33226Labels = mixedMoment B raw33226step0 raw33226step0Labels := by
      have ha : raw33226step0 = (fun i j => raw33226 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33226step0 raw33226; decide +kernel
      have hl : raw33226step0Labels = raw33226Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33226 raw33226Labels permutation664 permutation3
    mixedMoment B raw33226step0 raw33226step0Labels = mixedMoment B raw33226step1 raw33226step1Labels := by
      have ha : raw33226step1 = -raw33226step0 := by apply Matrix.ext; change ∀ i j, raw33226step1 i j = -(raw33226step0 i j); unfold raw33226step1 raw33226step0; decide +kernel
      have hl : raw33226step1Labels = raw33226step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1954 node1954Labels := by rfl

def raw33227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33227Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw33227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33227 raw33227Labels = mixedMoment B node1960 node1960Labels := by
  calc
    mixedMoment B raw33227 raw33227Labels = mixedMoment B raw33227step0 raw33227step0Labels := by
      have ha : raw33227step0 = (fun i j => raw33227 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33227step0 raw33227; decide +kernel
      have hl : raw33227step0Labels = raw33227Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33227 raw33227Labels permutation664 permutation3
    mixedMoment B raw33227step0 raw33227step0Labels = mixedMoment B raw33227step1 raw33227step1Labels := by
      have ha : raw33227step1 = -raw33227step0 := by apply Matrix.ext; change ∀ i j, raw33227step1 i j = -(raw33227step0 i j); unfold raw33227step1 raw33227step0; decide +kernel
      have hl : raw33227step1Labels = raw33227step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1960 node1960Labels := by rfl

def raw33228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33228Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33228 raw33228Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw33228 raw33228Labels = mixedMoment B raw33228step0 raw33228step0Labels := by
      have ha : raw33228step0 = (fun i j => raw33228 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33228step0 raw33228; decide +kernel
      have hl : raw33228step0Labels = raw33228Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33228 raw33228Labels permutation658 permutation3
    mixedMoment B raw33228step0 raw33228step0Labels = mixedMoment B raw33228step1 raw33228step1Labels := by
      have ha : raw33228step1 = -raw33228step0 := by apply Matrix.ext; change ∀ i j, raw33228step1 i j = -(raw33228step0 i j); unfold raw33228step1 raw33228step0; decide +kernel
      have hl : raw33228step1Labels = raw33228step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1987 node1987Labels := by rfl

def raw33229 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33229step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33229step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33229 raw33229Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw33229 raw33229Labels = mixedMoment B raw33229step0 raw33229step0Labels := by
      have ha : raw33229step0 = (fun i j => raw33229 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33229step0 raw33229; decide +kernel
      have hl : raw33229step0Labels = raw33229Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33229 raw33229Labels permutation152 permutation7
    mixedMoment B raw33229step0 raw33229step0Labels = mixedMoment B raw33229step1 raw33229step1Labels := by
      have ha : raw33229step1 = raw33229step0 := by apply Matrix.ext; unfold raw33229step1 raw33229step0; decide +kernel
      have hl : raw33229step0Labels = labelEmbedding10 ∘ raw33229step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33229step0 raw33229step0Labels raw33229step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw33230 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33230step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33230 raw33230Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw33230 raw33230Labels = mixedMoment B raw33230step0 raw33230step0Labels := by
      have hz : ∀ j, raw33230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33230step0 = (fun i j => raw33230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33230step0 raw33230; decide +kernel
      have hl : raw33230step0Labels = raw33230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33230 raw33230Labels permutation346 hz
    mixedMoment B raw33230step0 raw33230step0Labels = mixedMoment B raw33230step1 raw33230step1Labels := by
      have ha : raw33230step1 = (fun i j => raw33230step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33230step1 raw33230step0; decide +kernel
      have hl : raw33230step1Labels = raw33230step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33230step0 raw33230step0Labels permutation32 permutation7
    mixedMoment B raw33230step1 raw33230step1Labels = mixedMoment B raw33230step2 raw33230step2Labels := by
      have ha : raw33230step2 = raw33230step1 := by apply Matrix.ext; unfold raw33230step2 raw33230step1; decide +kernel
      have hl : raw33230step1Labels = labelEmbedding10 ∘ raw33230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33230step1 raw33230step1Labels raw33230step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw33231 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33231step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33231 raw33231Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw33231 raw33231Labels = mixedMoment B raw33231step0 raw33231step0Labels := by
      have ha : raw33231step0 = (fun i j => raw33231 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33231step0 raw33231; decide +kernel
      have hl : raw33231step0Labels = raw33231Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33231 raw33231Labels permutation154 permutation7
    mixedMoment B raw33231step0 raw33231step0Labels = mixedMoment B raw33231step1 raw33231step1Labels := by
      have ha : raw33231step1 = raw33231step0 := by apply Matrix.ext; unfold raw33231step1 raw33231step0; decide +kernel
      have hl : raw33231step0Labels = labelEmbedding10 ∘ raw33231step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33231step0 raw33231step0Labels raw33231step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw33232 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33232step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33232 raw33232Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw33232 raw33232Labels = mixedMoment B raw33232step0 raw33232step0Labels := by
      have ha : raw33232step0 = (fun i j => raw33232 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33232step0 raw33232; decide +kernel
      have hl : raw33232step0Labels = raw33232Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33232 raw33232Labels permutation152 permutation7
    mixedMoment B raw33232step0 raw33232step0Labels = mixedMoment B raw33232step1 raw33232step1Labels := by
      have ha : raw33232step1 = raw33232step0 := by apply Matrix.ext; unfold raw33232step1 raw33232step0; decide +kernel
      have hl : raw33232step0Labels = labelEmbedding10 ∘ raw33232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33232step0 raw33232step0Labels raw33232step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw33233 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw33233step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33233step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33233step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33233step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33233 raw33233Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw33233 raw33233Labels = mixedMoment B raw33233step0 raw33233step0Labels := by
      have ha : raw33233step0 = (fun i j => raw33233 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33233step0 raw33233; decide +kernel
      have hl : raw33233step0Labels = raw33233Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33233 raw33233Labels permutation160 permutation4
    mixedMoment B raw33233step0 raw33233step0Labels = mixedMoment B raw33233step1 raw33233step1Labels := by
      have ha : raw33233step1 = -raw33233step0 := by apply Matrix.ext; change ∀ i j, raw33233step1 i j = -(raw33233step0 i j); unfold raw33233step1 raw33233step0; decide +kernel
      have hl : raw33233step1Labels = raw33233step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33233step1 raw33233step1Labels = mixedMoment B raw33233step2 raw33233step2Labels := by
      have ha : raw33233step2 = raw33233step1 := by apply Matrix.ext; unfold raw33233step2 raw33233step1; decide +kernel
      have hl : raw33233step1Labels = labelEmbedding7 ∘ raw33233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33233step1 raw33233step1Labels raw33233step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

def raw33234 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33234step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33234step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33234 raw33234Labels = mixedMoment B node5004 node5004Labels := by
  calc
    mixedMoment B raw33234 raw33234Labels = mixedMoment B raw33234step0 raw33234step0Labels := by
      have ha : raw33234step0 = (fun i j => raw33234 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33234step0 raw33234; decide +kernel
      have hl : raw33234step0Labels = raw33234Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33234 raw33234Labels permutation152 permutation6
    mixedMoment B raw33234step0 raw33234step0Labels = mixedMoment B raw33234step1 raw33234step1Labels := by
      have ha : raw33234step1 = raw33234step0 := by apply Matrix.ext; unfold raw33234step1 raw33234step0; decide +kernel
      have hl : raw33234step0Labels = labelEmbedding9 ∘ raw33234step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33234step0 raw33234step0Labels raw33234step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5004 node5004Labels := by rfl

def raw33235 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33235step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33235 raw33235Labels = mixedMoment B node5082 node5082Labels := by
  calc
    mixedMoment B raw33235 raw33235Labels = mixedMoment B raw33235step0 raw33235step0Labels := by
      have ha : raw33235step0 = (fun i j => raw33235 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33235step0 raw33235; decide +kernel
      have hl : raw33235step0Labels = raw33235Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33235 raw33235Labels permutation152 permutation6
    mixedMoment B raw33235step0 raw33235step0Labels = mixedMoment B raw33235step1 raw33235step1Labels := by
      have ha : raw33235step1 = raw33235step0 := by apply Matrix.ext; unfold raw33235step1 raw33235step0; decide +kernel
      have hl : raw33235step0Labels = labelEmbedding9 ∘ raw33235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33235step0 raw33235step0Labels raw33235step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5082 node5082Labels := by rfl

def raw33236 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33236step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33236 raw33236Labels = mixedMoment B node5082 node5082Labels := by
  calc
    mixedMoment B raw33236 raw33236Labels = mixedMoment B raw33236step0 raw33236step0Labels := by
      have ha : raw33236step0 = (fun i j => raw33236 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33236step0 raw33236; decide +kernel
      have hl : raw33236step0Labels = raw33236Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33236 raw33236Labels permutation154 permutation6
    mixedMoment B raw33236step0 raw33236step0Labels = mixedMoment B raw33236step1 raw33236step1Labels := by
      have ha : raw33236step1 = raw33236step0 := by apply Matrix.ext; unfold raw33236step1 raw33236step0; decide +kernel
      have hl : raw33236step0Labels = labelEmbedding9 ∘ raw33236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33236step0 raw33236step0Labels raw33236step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5082 node5082Labels := by rfl

def raw33237 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33237step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33237step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33237step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33237 raw33237Labels = mixedMoment B node4736 node4736Labels := by
  calc
    mixedMoment B raw33237 raw33237Labels = mixedMoment B raw33237step0 raw33237step0Labels := by
      have ha : raw33237step0 = (fun i j => raw33237 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33237step0 raw33237; decide +kernel
      have hl : raw33237step0Labels = raw33237Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33237 raw33237Labels permutation158 permutation4
    mixedMoment B raw33237step0 raw33237step0Labels = mixedMoment B raw33237step1 raw33237step1Labels := by
      have ha : raw33237step1 = -raw33237step0 := by apply Matrix.ext; change ∀ i j, raw33237step1 i j = -(raw33237step0 i j); unfold raw33237step1 raw33237step0; decide +kernel
      have hl : raw33237step1Labels = raw33237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33237step1 raw33237step1Labels = mixedMoment B raw33237step2 raw33237step2Labels := by
      have ha : raw33237step2 = raw33237step1 := by apply Matrix.ext; unfold raw33237step2 raw33237step1; decide +kernel
      have hl : raw33237step1Labels = labelEmbedding7 ∘ raw33237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33237step1 raw33237step1Labels raw33237step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4736 node4736Labels := by rfl

def raw33238 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33238step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33238 raw33238Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw33238 raw33238Labels = mixedMoment B raw33238step0 raw33238step0Labels := by
      have ha : raw33238step0 = (fun i j => raw33238 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33238step0 raw33238; decide +kernel
      have hl : raw33238step0Labels = raw33238Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33238 raw33238Labels permutation152 permutation6
    mixedMoment B raw33238step0 raw33238step0Labels = mixedMoment B raw33238step1 raw33238step1Labels := by
      have ha : raw33238step1 = raw33238step0 := by apply Matrix.ext; unfold raw33238step1 raw33238step0; decide +kernel
      have hl : raw33238step0Labels = labelEmbedding9 ∘ raw33238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33238step0 raw33238step0Labels raw33238step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw33239 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33239step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33239step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33239step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33239 raw33239Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw33239 raw33239Labels = mixedMoment B raw33239step0 raw33239step0Labels := by
      have hz : ∀ j, raw33239 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33239step0 = (fun i j => raw33239 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33239step0 raw33239; decide +kernel
      have hl : raw33239step0Labels = raw33239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33239 raw33239Labels permutation346 hz
    mixedMoment B raw33239step0 raw33239step0Labels = mixedMoment B raw33239step1 raw33239step1Labels := by
      have ha : raw33239step1 = (fun i j => raw33239step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33239step1 raw33239step0; decide +kernel
      have hl : raw33239step1Labels = raw33239step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33239step0 raw33239step0Labels permutation32 permutation6
    mixedMoment B raw33239step1 raw33239step1Labels = mixedMoment B raw33239step2 raw33239step2Labels := by
      have ha : raw33239step2 = raw33239step1 := by apply Matrix.ext; unfold raw33239step2 raw33239step1; decide +kernel
      have hl : raw33239step1Labels = labelEmbedding9 ∘ raw33239step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33239step1 raw33239step1Labels raw33239step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw33240 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33240step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33240 raw33240Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw33240 raw33240Labels = mixedMoment B raw33240step0 raw33240step0Labels := by
      have ha : raw33240step0 = (fun i j => raw33240 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33240step0 raw33240; decide +kernel
      have hl : raw33240step0Labels = raw33240Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33240 raw33240Labels permutation152 permutation6
    mixedMoment B raw33240step0 raw33240step0Labels = mixedMoment B raw33240step1 raw33240step1Labels := by
      have ha : raw33240step1 = raw33240step0 := by apply Matrix.ext; unfold raw33240step1 raw33240step0; decide +kernel
      have hl : raw33240step0Labels = labelEmbedding9 ∘ raw33240step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33240step0 raw33240step0Labels raw33240step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw33241 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw33241step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33241step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33241step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33241 raw33241Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw33241 raw33241Labels = mixedMoment B raw33241step0 raw33241step0Labels := by
      have ha : raw33241step0 = (fun i j => raw33241 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33241step0 raw33241; decide +kernel
      have hl : raw33241step0Labels = raw33241Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33241 raw33241Labels permutation160 permutation4
    mixedMoment B raw33241step0 raw33241step0Labels = mixedMoment B raw33241step1 raw33241step1Labels := by
      have ha : raw33241step1 = -raw33241step0 := by apply Matrix.ext; change ∀ i j, raw33241step1 i j = -(raw33241step0 i j); unfold raw33241step1 raw33241step0; decide +kernel
      have hl : raw33241step1Labels = raw33241step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33241step1 raw33241step1Labels = mixedMoment B raw33241step2 raw33241step2Labels := by
      have ha : raw33241step2 = raw33241step1 := by apply Matrix.ext; unfold raw33241step2 raw33241step1; decide +kernel
      have hl : raw33241step1Labels = labelEmbedding7 ∘ raw33241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33241step1 raw33241step1Labels raw33241step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

def raw33242 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33242step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33242 raw33242Labels = mixedMoment B node4995 node4995Labels := by
  calc
    mixedMoment B raw33242 raw33242Labels = mixedMoment B raw33242step0 raw33242step0Labels := by
      have ha : raw33242step0 = (fun i j => raw33242 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33242step0 raw33242; decide +kernel
      have hl : raw33242step0Labels = raw33242Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33242 raw33242Labels permutation152 permutation6
    mixedMoment B raw33242step0 raw33242step0Labels = mixedMoment B raw33242step1 raw33242step1Labels := by
      have ha : raw33242step1 = raw33242step0 := by apply Matrix.ext; unfold raw33242step1 raw33242step0; decide +kernel
      have hl : raw33242step0Labels = labelEmbedding9 ∘ raw33242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33242step0 raw33242step0Labels raw33242step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4995 node4995Labels := by rfl

def raw33243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33243step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33243 raw33243Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw33243 raw33243Labels = mixedMoment B raw33243step0 raw33243step0Labels := by
      have hz : ∀ j, raw33243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33243step0 = (fun i j => raw33243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33243step0 raw33243; decide +kernel
      have hl : raw33243step0Labels = raw33243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33243 raw33243Labels permutation346 hz
    mixedMoment B raw33243step0 raw33243step0Labels = mixedMoment B raw33243step1 raw33243step1Labels := by
      have ha : raw33243step1 = (fun i j => raw33243step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33243step1 raw33243step0; decide +kernel
      have hl : raw33243step1Labels = raw33243step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33243step0 raw33243step0Labels permutation32 permutation6
    mixedMoment B raw33243step1 raw33243step1Labels = mixedMoment B raw33243step2 raw33243step2Labels := by
      have ha : raw33243step2 = raw33243step1 := by apply Matrix.ext; unfold raw33243step2 raw33243step1; decide +kernel
      have hl : raw33243step1Labels = labelEmbedding9 ∘ raw33243step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33243step1 raw33243step1Labels raw33243step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw33244 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33244step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33244 raw33244Labels = mixedMoment B node5069 node5069Labels := by
  calc
    mixedMoment B raw33244 raw33244Labels = mixedMoment B raw33244step0 raw33244step0Labels := by
      have ha : raw33244step0 = (fun i j => raw33244 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33244step0 raw33244; decide +kernel
      have hl : raw33244step0Labels = raw33244Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33244 raw33244Labels permutation152 permutation6
    mixedMoment B raw33244step0 raw33244step0Labels = mixedMoment B raw33244step1 raw33244step1Labels := by
      have ha : raw33244step1 = raw33244step0 := by apply Matrix.ext; unfold raw33244step1 raw33244step0; decide +kernel
      have hl : raw33244step0Labels = labelEmbedding9 ∘ raw33244step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33244step0 raw33244step0Labels raw33244step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5069 node5069Labels := by rfl

def raw33245 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw33245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33245step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33245 raw33245Labels = mixedMoment B node5069 node5069Labels := by
  calc
    mixedMoment B raw33245 raw33245Labels = mixedMoment B raw33245step0 raw33245step0Labels := by
      have ha : raw33245step0 = (fun i j => raw33245 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33245step0 raw33245; decide +kernel
      have hl : raw33245step0Labels = raw33245Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33245 raw33245Labels permutation154 permutation6
    mixedMoment B raw33245step0 raw33245step0Labels = mixedMoment B raw33245step1 raw33245step1Labels := by
      have ha : raw33245step1 = raw33245step0 := by apply Matrix.ext; unfold raw33245step1 raw33245step0; decide +kernel
      have hl : raw33245step0Labels = labelEmbedding9 ∘ raw33245step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33245step0 raw33245step0Labels raw33245step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5069 node5069Labels := by rfl

def raw33246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33246step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33246 raw33246Labels = mixedMoment B node4917 node4917Labels := by
  calc
    mixedMoment B raw33246 raw33246Labels = mixedMoment B raw33246step0 raw33246step0Labels := by
      have ha : raw33246step0 = (fun i j => raw33246 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33246step0 raw33246; decide +kernel
      have hl : raw33246step0Labels = raw33246Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33246 raw33246Labels permutation154 permutation3
    mixedMoment B raw33246step0 raw33246step0Labels = mixedMoment B raw33246step1 raw33246step1Labels := by
      have ha : raw33246step1 = raw33246step0 := by apply Matrix.ext; unfold raw33246step1 raw33246step0; decide +kernel
      have hl : raw33246step0Labels = labelEmbedding6 ∘ raw33246step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33246step0 raw33246step0Labels raw33246step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4917 node4917Labels := by rfl

def raw33247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw33247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw33247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33247step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33247 raw33247Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw33247 raw33247Labels = mixedMoment B raw33247step0 raw33247step0Labels := by
      have hz : ∀ j, raw33247 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33247step0 = (fun i j => raw33247 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33247step0 raw33247; decide +kernel
      have hl : raw33247step0Labels = raw33247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33247 raw33247Labels permutation520 hz
    mixedMoment B raw33247step0 raw33247step0Labels = mixedMoment B raw33247step1 raw33247step1Labels := by
      have ha : raw33247step1 = (fun i j => raw33247step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33247step1 raw33247step0; decide +kernel
      have hl : raw33247step1Labels = raw33247step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33247step0 raw33247step0Labels permutation32 permutation3
    mixedMoment B raw33247step1 raw33247step1Labels = mixedMoment B raw33247step2 raw33247step2Labels := by
      have ha : raw33247step2 = raw33247step1 := by apply Matrix.ext; unfold raw33247step2 raw33247step1; decide +kernel
      have hl : raw33247step1Labels = labelEmbedding6 ∘ raw33247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33247step1 raw33247step1Labels raw33247step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw33248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw33248step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw33248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33248 raw33248Labels = mixedMoment B node4920 node4920Labels := by
  calc
    mixedMoment B raw33248 raw33248Labels = mixedMoment B raw33248step0 raw33248step0Labels := by
      have hz : ∀ j, raw33248 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33248step0 = (fun i j => raw33248 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33248step0 raw33248; decide +kernel
      have hl : raw33248step0Labels = raw33248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33248 raw33248Labels permutation346 hz
    mixedMoment B raw33248step0 raw33248step0Labels = mixedMoment B raw33248step1 raw33248step1Labels := by
      have ha : raw33248step1 = (fun i j => raw33248step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33248step1 raw33248step0; decide +kernel
      have hl : raw33248step1Labels = raw33248step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33248step0 raw33248step0Labels permutation35 permutation3
    mixedMoment B raw33248step1 raw33248step1Labels = mixedMoment B raw33248step2 raw33248step2Labels := by
      have ha : raw33248step2 = raw33248step1 := by apply Matrix.ext; unfold raw33248step2 raw33248step1; decide +kernel
      have hl : raw33248step1Labels = labelEmbedding6 ∘ raw33248step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33248step1 raw33248step1Labels raw33248step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4920 node4920Labels := by rfl

def raw33249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw33249step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw33249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33249 raw33249Labels = mixedMoment B node5028 node5028Labels := by
  calc
    mixedMoment B raw33249 raw33249Labels = mixedMoment B raw33249step0 raw33249step0Labels := by
      have ha : raw33249step0 = (fun i j => raw33249 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33249step0 raw33249; decide +kernel
      have hl : raw33249step0Labels = raw33249Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33249 raw33249Labels permutation155 permutation3
    mixedMoment B raw33249step0 raw33249step0Labels = mixedMoment B raw33249step1 raw33249step1Labels := by
      have ha : raw33249step1 = raw33249step0 := by apply Matrix.ext; unfold raw33249step1 raw33249step0; decide +kernel
      have hl : raw33249step0Labels = labelEmbedding6 ∘ raw33249step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33249step0 raw33249step0Labels raw33249step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5028 node5028Labels := by rfl

def raw33250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![2, 0, -2]]
def raw33250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw33250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw33250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw33250step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33250step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw33250step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33250 raw33250Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw33250 raw33250Labels = mixedMoment B raw33250step0 raw33250step0Labels := by
      have hz : ∀ j, raw33250 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33250step0 = (fun i j => raw33250 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33250step0 raw33250; decide +kernel
      have hl : raw33250step0Labels = raw33250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33250 raw33250Labels permutation520 hz
    mixedMoment B raw33250step0 raw33250step0Labels = mixedMoment B raw33250step1 raw33250step1Labels := by
      have hz : ∀ j, raw33250step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33250step1 = (fun i j => raw33250step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33250step1 raw33250step0; decide +kernel
      have hl : raw33250step1Labels = raw33250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33250step0 raw33250step0Labels permutation80 hz
    mixedMoment B raw33250step1 raw33250step1Labels = mixedMoment B raw33250step2 raw33250step2Labels := by
      have ha : raw33250step2 = (fun i j => raw33250step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33250step2 raw33250step1; decide +kernel
      have hl : raw33250step2Labels = raw33250step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33250step1 raw33250step1Labels permutation9 permutation3
    mixedMoment B raw33250step2 raw33250step2Labels = mixedMoment B raw33250step3 raw33250step3Labels := by
      have ha : raw33250step3 = raw33250step2 := by apply Matrix.ext; unfold raw33250step3 raw33250step2; decide +kernel
      have hl : raw33250step2Labels = labelEmbedding6 ∘ raw33250step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33250step2 raw33250step2Labels raw33250step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw33251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw33251step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw33251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33251 raw33251Labels = mixedMoment B node4922 node4922Labels := by
  calc
    mixedMoment B raw33251 raw33251Labels = mixedMoment B raw33251step0 raw33251step0Labels := by
      have hz : ∀ j, raw33251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33251step0 = (fun i j => raw33251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33251step0 raw33251; decide +kernel
      have hl : raw33251step0Labels = raw33251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33251 raw33251Labels permutation346 hz
    mixedMoment B raw33251step0 raw33251step0Labels = mixedMoment B raw33251step1 raw33251step1Labels := by
      have ha : raw33251step1 = (fun i j => raw33251step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33251step1 raw33251step0; decide +kernel
      have hl : raw33251step1Labels = raw33251step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33251step0 raw33251step0Labels permutation33 permutation3
    mixedMoment B raw33251step1 raw33251step1Labels = mixedMoment B raw33251step2 raw33251step2Labels := by
      have ha : raw33251step2 = raw33251step1 := by apply Matrix.ext; unfold raw33251step2 raw33251step1; decide +kernel
      have hl : raw33251step1Labels = labelEmbedding6 ∘ raw33251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33251step1 raw33251step1Labels raw33251step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4922 node4922Labels := by rfl

def raw33252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw33252step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw33252step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33252 raw33252Labels = mixedMoment B node5030 node5030Labels := by
  calc
    mixedMoment B raw33252 raw33252Labels = mixedMoment B raw33252step0 raw33252step0Labels := by
      have ha : raw33252step0 = (fun i j => raw33252 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33252step0 raw33252; decide +kernel
      have hl : raw33252step0Labels = raw33252Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33252 raw33252Labels permutation153 permutation3
    mixedMoment B raw33252step0 raw33252step0Labels = mixedMoment B raw33252step1 raw33252step1Labels := by
      have ha : raw33252step1 = raw33252step0 := by apply Matrix.ext; unfold raw33252step1 raw33252step0; decide +kernel
      have hl : raw33252step0Labels = labelEmbedding6 ∘ raw33252step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33252step0 raw33252step0Labels raw33252step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5030 node5030Labels := by rfl

def raw33253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw33253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw33253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw33253step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw33253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33253 raw33253Labels = mixedMoment B node4919 node4919Labels := by
  calc
    mixedMoment B raw33253 raw33253Labels = mixedMoment B raw33253step0 raw33253step0Labels := by
      have hz : ∀ j, raw33253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33253step0 = (fun i j => raw33253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33253step0 raw33253; decide +kernel
      have hl : raw33253step0Labels = raw33253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33253 raw33253Labels permutation346 hz
    mixedMoment B raw33253step0 raw33253step0Labels = mixedMoment B raw33253step1 raw33253step1Labels := by
      have ha : raw33253step1 = (fun i j => raw33253step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33253step1 raw33253step0; decide +kernel
      have hl : raw33253step1Labels = raw33253step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33253step0 raw33253step0Labels permutation34 permutation3
    mixedMoment B raw33253step1 raw33253step1Labels = mixedMoment B raw33253step2 raw33253step2Labels := by
      have ha : raw33253step2 = raw33253step1 := by apply Matrix.ext; unfold raw33253step2 raw33253step1; decide +kernel
      have hl : raw33253step1Labels = labelEmbedding6 ∘ raw33253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33253step1 raw33253step1Labels raw33253step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4919 node4919Labels := by rfl

def raw33254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw33254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw33254step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw33254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33254 raw33254Labels = mixedMoment B node5027 node5027Labels := by
  calc
    mixedMoment B raw33254 raw33254Labels = mixedMoment B raw33254step0 raw33254step0Labels := by
      have ha : raw33254step0 = (fun i j => raw33254 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33254step0 raw33254; decide +kernel
      have hl : raw33254step0Labels = raw33254Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33254 raw33254Labels permutation154 permutation3
    mixedMoment B raw33254step0 raw33254step0Labels = mixedMoment B raw33254step1 raw33254step1Labels := by
      have ha : raw33254step1 = raw33254step0 := by apply Matrix.ext; unfold raw33254step1 raw33254step0; decide +kernel
      have hl : raw33254step0Labels = labelEmbedding6 ∘ raw33254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33254step0 raw33254step0Labels raw33254step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5027 node5027Labels := by rfl

def raw33255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, -1, -2]]
def raw33255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw33255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw33255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw33255step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33255step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw33255step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33255 raw33255Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw33255 raw33255Labels = mixedMoment B raw33255step0 raw33255step0Labels := by
      have hz : ∀ j, raw33255 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33255step0 = (fun i j => raw33255 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33255step0 raw33255; decide +kernel
      have hl : raw33255step0Labels = raw33255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33255 raw33255Labels permutation520 hz
    mixedMoment B raw33255step0 raw33255step0Labels = mixedMoment B raw33255step1 raw33255step1Labels := by
      have hz : ∀ j, raw33255step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33255step1 = (fun i j => raw33255step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33255step1 raw33255step0; decide +kernel
      have hl : raw33255step1Labels = raw33255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33255step0 raw33255step0Labels permutation80 hz
    mixedMoment B raw33255step1 raw33255step1Labels = mixedMoment B raw33255step2 raw33255step2Labels := by
      have ha : raw33255step2 = (fun i j => raw33255step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33255step2 raw33255step1; decide +kernel
      have hl : raw33255step2Labels = raw33255step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33255step1 raw33255step1Labels permutation8 permutation3
    mixedMoment B raw33255step2 raw33255step2Labels = mixedMoment B raw33255step3 raw33255step3Labels := by
      have ha : raw33255step3 = raw33255step2 := by apply Matrix.ext; unfold raw33255step3 raw33255step2; decide +kernel
      have hl : raw33255step2Labels = labelEmbedding6 ∘ raw33255step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33255step2 raw33255step2Labels raw33255step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw33256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33256 raw33256Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw33256 raw33256Labels = mixedMoment B raw33256step0 raw33256step0Labels := by
      have hz : ∀ j, raw33256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33256step0 = (fun i j => raw33256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33256step0 raw33256; decide +kernel
      have hl : raw33256step0Labels = raw33256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33256 raw33256Labels permutation346 hz
    mixedMoment B raw33256step0 raw33256step0Labels = mixedMoment B raw33256step1 raw33256step1Labels := by
      have ha : raw33256step1 = (fun i j => raw33256step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33256step1 raw33256step0; decide +kernel
      have hl : raw33256step1Labels = raw33256step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33256step0 raw33256step0Labels permutation58 permutation3
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw33257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33257 raw33257Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw33257 raw33257Labels = mixedMoment B raw33257step0 raw33257step0Labels := by
      have ha : raw33257step0 = (fun i j => raw33257 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33257step0 raw33257; decide +kernel
      have hl : raw33257step0Labels = raw33257Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33257 raw33257Labels permutation154 permutation3
    _ = mixedMoment B node3964 node3964Labels := by rfl

def raw33258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw33258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw33258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw33258step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33258step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw33258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33258 raw33258Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw33258 raw33258Labels = mixedMoment B raw33258step0 raw33258step0Labels := by
      have hz : ∀ j, raw33258 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33258step0 = (fun i j => raw33258 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33258step0 raw33258; decide +kernel
      have hl : raw33258step0Labels = raw33258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33258 raw33258Labels permutation520 hz
    mixedMoment B raw33258step0 raw33258step0Labels = mixedMoment B raw33258step1 raw33258step1Labels := by
      have hz : ∀ j, raw33258step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33258step1 = (fun i j => raw33258step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33258step1 raw33258step0; decide +kernel
      have hl : raw33258step1Labels = raw33258step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33258step0 raw33258step0Labels permutation80 hz
    mixedMoment B raw33258step1 raw33258step1Labels = mixedMoment B raw33258step2 raw33258step2Labels := by
      have ha : raw33258step2 = (fun i j => raw33258step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33258step2 raw33258step1; decide +kernel
      have hl : raw33258step2Labels = raw33258step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33258step1 raw33258step1Labels permutation8 permutation3
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw33259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33259 raw33259Labels = mixedMoment B node2308 node2308Labels := by
  calc
    mixedMoment B raw33259 raw33259Labels = mixedMoment B raw33259step0 raw33259step0Labels := by
      have ha : raw33259step0 = (fun i j => raw33259 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33259step0 raw33259; decide +kernel
      have hl : raw33259step0Labels = raw33259Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33259 raw33259Labels permutation154 permutation3
    _ = mixedMoment B node2308 node2308Labels := by rfl

def raw33260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw33260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw33260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33260 raw33260Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw33260 raw33260Labels = mixedMoment B raw33260step0 raw33260step0Labels := by
      have hz : ∀ j, raw33260 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33260step0 = (fun i j => raw33260 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33260step0 raw33260; decide +kernel
      have hl : raw33260step0Labels = raw33260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33260 raw33260Labels permutation520 hz
    mixedMoment B raw33260step0 raw33260step0Labels = mixedMoment B raw33260step1 raw33260step1Labels := by
      have ha : raw33260step1 = (fun i j => raw33260step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33260step1 raw33260step0; decide +kernel
      have hl : raw33260step1Labels = raw33260step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33260step0 raw33260step0Labels permutation32 permutation3
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw33261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw33261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33261 raw33261Labels = mixedMoment B node2311 node2311Labels := by
  calc
    mixedMoment B raw33261 raw33261Labels = mixedMoment B raw33261step0 raw33261step0Labels := by
      have hz : ∀ j, raw33261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33261step0 = (fun i j => raw33261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33261step0 raw33261; decide +kernel
      have hl : raw33261step0Labels = raw33261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33261 raw33261Labels permutation346 hz
    mixedMoment B raw33261step0 raw33261step0Labels = mixedMoment B raw33261step1 raw33261step1Labels := by
      have ha : raw33261step1 = (fun i j => raw33261step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33261step1 raw33261step0; decide +kernel
      have hl : raw33261step1Labels = raw33261step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33261step0 raw33261step0Labels permutation35 permutation3
    _ = mixedMoment B node2311 node2311Labels := by rfl

def raw33262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw33262step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33262 raw33262Labels = mixedMoment B node2417 node2417Labels := by
  calc
    mixedMoment B raw33262 raw33262Labels = mixedMoment B raw33262step0 raw33262step0Labels := by
      have ha : raw33262step0 = (fun i j => raw33262 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33262step0 raw33262; decide +kernel
      have hl : raw33262step0Labels = raw33262Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33262 raw33262Labels permutation155 permutation3
    _ = mixedMoment B node2417 node2417Labels := by rfl

def raw33263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![2, 0, -2]]
def raw33263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw33263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw33263step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw33263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33263 raw33263Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw33263 raw33263Labels = mixedMoment B raw33263step0 raw33263step0Labels := by
      have hz : ∀ j, raw33263 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33263step0 = (fun i j => raw33263 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33263step0 raw33263; decide +kernel
      have hl : raw33263step0Labels = raw33263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33263 raw33263Labels permutation520 hz
    mixedMoment B raw33263step0 raw33263step0Labels = mixedMoment B raw33263step1 raw33263step1Labels := by
      have hz : ∀ j, raw33263step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33263step1 = (fun i j => raw33263step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33263step1 raw33263step0; decide +kernel
      have hl : raw33263step1Labels = raw33263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33263step0 raw33263step0Labels permutation80 hz
    mixedMoment B raw33263step1 raw33263step1Labels = mixedMoment B raw33263step2 raw33263step2Labels := by
      have ha : raw33263step2 = (fun i j => raw33263step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33263step2 raw33263step1; decide +kernel
      have hl : raw33263step2Labels = raw33263step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33263step1 raw33263step1Labels permutation9 permutation3
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw33264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw33264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33264 raw33264Labels = mixedMoment B node2313 node2313Labels := by
  calc
    mixedMoment B raw33264 raw33264Labels = mixedMoment B raw33264step0 raw33264step0Labels := by
      have hz : ∀ j, raw33264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33264step0 = (fun i j => raw33264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33264step0 raw33264; decide +kernel
      have hl : raw33264step0Labels = raw33264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33264 raw33264Labels permutation346 hz
    mixedMoment B raw33264step0 raw33264step0Labels = mixedMoment B raw33264step1 raw33264step1Labels := by
      have ha : raw33264step1 = (fun i j => raw33264step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33264step1 raw33264step0; decide +kernel
      have hl : raw33264step1Labels = raw33264step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33264step0 raw33264step0Labels permutation33 permutation3
    _ = mixedMoment B node2313 node2313Labels := by rfl

def raw33265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw33265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33265 raw33265Labels = mixedMoment B node2419 node2419Labels := by
  calc
    mixedMoment B raw33265 raw33265Labels = mixedMoment B raw33265step0 raw33265step0Labels := by
      have ha : raw33265step0 = (fun i j => raw33265 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33265step0 raw33265; decide +kernel
      have hl : raw33265step0Labels = raw33265Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33265 raw33265Labels permutation153 permutation3
    _ = mixedMoment B node2419 node2419Labels := by rfl

def raw33266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw33266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw33266step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw33266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33266 raw33266Labels = mixedMoment B node2310 node2310Labels := by
  calc
    mixedMoment B raw33266 raw33266Labels = mixedMoment B raw33266step0 raw33266step0Labels := by
      have hz : ∀ j, raw33266 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33266step0 = (fun i j => raw33266 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33266step0 raw33266; decide +kernel
      have hl : raw33266step0Labels = raw33266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33266 raw33266Labels permutation346 hz
    mixedMoment B raw33266step0 raw33266step0Labels = mixedMoment B raw33266step1 raw33266step1Labels := by
      have ha : raw33266step1 = (fun i j => raw33266step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33266step1 raw33266step0; decide +kernel
      have hl : raw33266step1Labels = raw33266step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33266step0 raw33266step0Labels permutation34 permutation3
    _ = mixedMoment B node2310 node2310Labels := by rfl

def raw33267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw33267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw33267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33267 raw33267Labels = mixedMoment B node2416 node2416Labels := by
  calc
    mixedMoment B raw33267 raw33267Labels = mixedMoment B raw33267step0 raw33267step0Labels := by
      have ha : raw33267step0 = (fun i j => raw33267 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33267step0 raw33267; decide +kernel
      have hl : raw33267step0Labels = raw33267Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33267 raw33267Labels permutation154 permutation3
    _ = mixedMoment B node2416 node2416Labels := by rfl

def raw33268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, -1, -2]]
def raw33268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw33268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw33268step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33268step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw33268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33268 raw33268Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw33268 raw33268Labels = mixedMoment B raw33268step0 raw33268step0Labels := by
      have hz : ∀ j, raw33268 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33268step0 = (fun i j => raw33268 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33268step0 raw33268; decide +kernel
      have hl : raw33268step0Labels = raw33268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33268 raw33268Labels permutation520 hz
    mixedMoment B raw33268step0 raw33268step0Labels = mixedMoment B raw33268step1 raw33268step1Labels := by
      have hz : ∀ j, raw33268step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33268step1 = (fun i j => raw33268step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33268step1 raw33268step0; decide +kernel
      have hl : raw33268step1Labels = raw33268step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33268step0 raw33268step0Labels permutation80 hz
    mixedMoment B raw33268step1 raw33268step1Labels = mixedMoment B raw33268step2 raw33268step2Labels := by
      have ha : raw33268step2 = (fun i j => raw33268step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33268step2 raw33268step1; decide +kernel
      have hl : raw33268step2Labels = raw33268step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33268step1 raw33268step1Labels permutation8 permutation3
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw33269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33269step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33269 raw33269Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw33269 raw33269Labels = mixedMoment B raw33269step0 raw33269step0Labels := by
      have hz : ∀ j, raw33269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33269step0 = (fun i j => raw33269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33269step0 raw33269; decide +kernel
      have hl : raw33269step0Labels = raw33269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33269 raw33269Labels permutation346 hz
    mixedMoment B raw33269step0 raw33269step0Labels = mixedMoment B raw33269step1 raw33269step1Labels := by
      have ha : raw33269step1 = (fun i j => raw33269step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33269step1 raw33269step0; decide +kernel
      have hl : raw33269step1Labels = raw33269step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33269step0 raw33269step0Labels permutation58 permutation3
    mixedMoment B raw33269step1 raw33269step1Labels = mixedMoment B raw33269step2 raw33269step2Labels := by
      have ha : raw33269step2 = raw33269step1 := by apply Matrix.ext; unfold raw33269step2 raw33269step1; decide +kernel
      have hl : raw33269step1Labels = labelEmbedding6 ∘ raw33269step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33269step1 raw33269step1Labels raw33269step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw33270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33270step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33270step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33270step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33270step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33270 raw33270Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw33270 raw33270Labels = mixedMoment B raw33270step0 raw33270step0Labels := by
      have ha : raw33270step0 = (fun i j => raw33270 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33270step0 raw33270; decide +kernel
      have hl : raw33270step0Labels = raw33270Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33270 raw33270Labels permutation662 permutation3
    mixedMoment B raw33270step0 raw33270step0Labels = mixedMoment B raw33270step1 raw33270step1Labels := by
      have ha : raw33270step1 = -raw33270step0 := by apply Matrix.ext; change ∀ i j, raw33270step1 i j = -(raw33270step0 i j); unfold raw33270step1 raw33270step0; decide +kernel
      have hl : raw33270step1Labels = raw33270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33270step1 raw33270step1Labels = mixedMoment B raw33270step2 raw33270step2Labels := by
      have ha : raw33270step2 = raw33270step1 := by apply Matrix.ext; unfold raw33270step2 raw33270step1; decide +kernel
      have hl : raw33270step1Labels = labelEmbedding6 ∘ raw33270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33270step1 raw33270step1Labels raw33270step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw33271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw33271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw33271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33271step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33271step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33271step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33271step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33271 raw33271Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw33271 raw33271Labels = mixedMoment B raw33271step0 raw33271step0Labels := by
      have hz : ∀ j, raw33271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33271step0 = (fun i j => raw33271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33271step0 raw33271; decide +kernel
      have hl : raw33271step0Labels = raw33271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33271 raw33271Labels permutation346 hz
    mixedMoment B raw33271step0 raw33271step0Labels = mixedMoment B raw33271step1 raw33271step1Labels := by
      have ha : raw33271step1 = (fun i j => raw33271step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33271step1 raw33271step0; decide +kernel
      have hl : raw33271step1Labels = raw33271step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33271step0 raw33271step0Labels permutation145 permutation3
    mixedMoment B raw33271step1 raw33271step1Labels = mixedMoment B raw33271step2 raw33271step2Labels := by
      have ha : raw33271step2 = -raw33271step1 := by apply Matrix.ext; change ∀ i j, raw33271step2 i j = -(raw33271step1 i j); unfold raw33271step2 raw33271step1; decide +kernel
      have hl : raw33271step2Labels = raw33271step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33271step2 raw33271step2Labels = mixedMoment B raw33271step3 raw33271step3Labels := by
      have ha : raw33271step3 = raw33271step2 := by apply Matrix.ext; unfold raw33271step3 raw33271step2; decide +kernel
      have hl : raw33271step2Labels = labelEmbedding6 ∘ raw33271step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33271step2 raw33271step2Labels raw33271step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw33272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33272step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33272 raw33272Labels = mixedMoment B node4912 node4912Labels := by
  calc
    mixedMoment B raw33272 raw33272Labels = mixedMoment B raw33272step0 raw33272step0Labels := by
      have ha : raw33272step0 = (fun i j => raw33272 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33272step0 raw33272; decide +kernel
      have hl : raw33272step0Labels = raw33272Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33272 raw33272Labels permutation164 permutation3
    mixedMoment B raw33272step0 raw33272step0Labels = mixedMoment B raw33272step1 raw33272step1Labels := by
      have ha : raw33272step1 = raw33272step0 := by apply Matrix.ext; unfold raw33272step1 raw33272step0; decide +kernel
      have hl : raw33272step0Labels = labelEmbedding6 ∘ raw33272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33272step0 raw33272step0Labels raw33272step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4912 node4912Labels := by rfl

def raw33273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw33273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33273step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33273step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33273 raw33273Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw33273 raw33273Labels = mixedMoment B raw33273step0 raw33273step0Labels := by
      have ha : raw33273step0 = (fun i j => raw33273 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33273step0 raw33273; decide +kernel
      have hl : raw33273step0Labels = raw33273Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33273 raw33273Labels permutation164 permutation3
    mixedMoment B raw33273step0 raw33273step0Labels = mixedMoment B raw33273step1 raw33273step1Labels := by
      have ha : raw33273step1 = raw33273step0 := by apply Matrix.ext; unfold raw33273step1 raw33273step0; decide +kernel
      have hl : raw33273step0Labels = labelEmbedding6 ∘ raw33273step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33273step0 raw33273step0Labels raw33273step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw33274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33274step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33274 raw33274Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw33274 raw33274Labels = mixedMoment B raw33274step0 raw33274step0Labels := by
      have ha : raw33274step0 = (fun i j => raw33274 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33274step0 raw33274; decide +kernel
      have hl : raw33274step0Labels = raw33274Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33274 raw33274Labels permutation168 permutation3
    mixedMoment B raw33274step0 raw33274step0Labels = mixedMoment B raw33274step1 raw33274step1Labels := by
      have ha : raw33274step1 = raw33274step0 := by apply Matrix.ext; unfold raw33274step1 raw33274step0; decide +kernel
      have hl : raw33274step0Labels = labelEmbedding6 ∘ raw33274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33274step0 raw33274step0Labels raw33274step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw33275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw33275step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw33275step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33275 raw33275Labels = mixedMoment B node4914 node4914Labels := by
  calc
    mixedMoment B raw33275 raw33275Labels = mixedMoment B raw33275step0 raw33275step0Labels := by
      have hz : ∀ j, raw33275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33275step0 = (fun i j => raw33275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33275step0 raw33275; decide +kernel
      have hl : raw33275step0Labels = raw33275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33275 raw33275Labels permutation346 hz
    mixedMoment B raw33275step0 raw33275step0Labels = mixedMoment B raw33275step1 raw33275step1Labels := by
      have ha : raw33275step1 = (fun i j => raw33275step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33275step1 raw33275step0; decide +kernel
      have hl : raw33275step1Labels = raw33275step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33275step0 raw33275step0Labels permutation35 permutation3
    mixedMoment B raw33275step1 raw33275step1Labels = mixedMoment B raw33275step2 raw33275step2Labels := by
      have ha : raw33275step2 = raw33275step1 := by apply Matrix.ext; unfold raw33275step2 raw33275step1; decide +kernel
      have hl : raw33275step1Labels = labelEmbedding6 ∘ raw33275step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33275step1 raw33275step1Labels raw33275step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4914 node4914Labels := by rfl

def raw33276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33276step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33276 raw33276Labels = mixedMoment B node4989 node4989Labels := by
  calc
    mixedMoment B raw33276 raw33276Labels = mixedMoment B raw33276step0 raw33276step0Labels := by
      have ha : raw33276step0 = (fun i j => raw33276 (permutation517 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33276step0 raw33276; decide +kernel
      have hl : raw33276step0Labels = raw33276Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33276 raw33276Labels permutation517 permutation5
    mixedMoment B raw33276step0 raw33276step0Labels = mixedMoment B raw33276step1 raw33276step1Labels := by
      have ha : raw33276step1 = raw33276step0 := by apply Matrix.ext; unfold raw33276step1 raw33276step0; decide +kernel
      have hl : raw33276step0Labels = labelEmbedding8 ∘ raw33276step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33276step0 raw33276step0Labels raw33276step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4989 node4989Labels := by rfl

def raw33277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw33277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw33277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33277step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33277step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33277 raw33277Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw33277 raw33277Labels = mixedMoment B raw33277step0 raw33277step0Labels := by
      have hz : ∀ j, raw33277 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33277step0 = (fun i j => raw33277 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33277step0 raw33277; decide +kernel
      have hl : raw33277step0Labels = raw33277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33277 raw33277Labels permutation346 hz
    mixedMoment B raw33277step0 raw33277step0Labels = mixedMoment B raw33277step1 raw33277step1Labels := by
      have ha : raw33277step1 = (fun i j => raw33277step0 (permutation103 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33277step1 raw33277step0; decide +kernel
      have hl : raw33277step1Labels = raw33277step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33277step0 raw33277step0Labels permutation103 permutation5
    mixedMoment B raw33277step1 raw33277step1Labels = mixedMoment B raw33277step2 raw33277step2Labels := by
      have ha : raw33277step2 = raw33277step1 := by apply Matrix.ext; unfold raw33277step2 raw33277step1; decide +kernel
      have hl : raw33277step1Labels = labelEmbedding8 ∘ raw33277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33277step1 raw33277step1Labels raw33277step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw33278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33278step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33278 raw33278Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw33278 raw33278Labels = mixedMoment B raw33278step0 raw33278step0Labels := by
      have hz : ∀ j, raw33278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33278step0 = (fun i j => raw33278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33278step0 raw33278; decide +kernel
      have hl : raw33278step0Labels = raw33278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33278 raw33278Labels permutation346 hz
    mixedMoment B raw33278step0 raw33278step0Labels = mixedMoment B raw33278step1 raw33278step1Labels := by
      have ha : raw33278step1 = (fun i j => raw33278step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33278step1 raw33278step0; decide +kernel
      have hl : raw33278step1Labels = raw33278step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33278step0 raw33278step0Labels permutation35 permutation3
    mixedMoment B raw33278step1 raw33278step1Labels = mixedMoment B raw33278step2 raw33278step2Labels := by
      have ha : raw33278step2 = raw33278step1 := by apply Matrix.ext; unfold raw33278step2 raw33278step1; decide +kernel
      have hl : raw33278step1Labels = labelEmbedding6 ∘ raw33278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33278step1 raw33278step1Labels raw33278step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw33279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw33279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw33279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw33279step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw33279step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33279 raw33279Labels = mixedMoment B node4923 node4923Labels := by
  calc
    mixedMoment B raw33279 raw33279Labels = mixedMoment B raw33279step0 raw33279step0Labels := by
      have hz : ∀ j, raw33279 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33279step0 = (fun i j => raw33279 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33279step0 raw33279; decide +kernel
      have hl : raw33279step0Labels = raw33279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33279 raw33279Labels permutation346 hz
    mixedMoment B raw33279step0 raw33279step0Labels = mixedMoment B raw33279step1 raw33279step1Labels := by
      have ha : raw33279step1 = (fun i j => raw33279step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33279step1 raw33279step0; decide +kernel
      have hl : raw33279step1Labels = raw33279step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33279step0 raw33279step0Labels permutation32 permutation3
    mixedMoment B raw33279step1 raw33279step1Labels = mixedMoment B raw33279step2 raw33279step2Labels := by
      have ha : raw33279step2 = raw33279step1 := by apply Matrix.ext; unfold raw33279step2 raw33279step1; decide +kernel
      have hl : raw33279step1Labels = labelEmbedding6 ∘ raw33279step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33279step1 raw33279step1Labels raw33279step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4923 node4923Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
