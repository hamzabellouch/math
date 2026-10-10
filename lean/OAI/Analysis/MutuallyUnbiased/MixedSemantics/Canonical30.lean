import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3840 raw3840Labels = mixedMoment B node2083 node2083Labels := by
  calc
    mixedMoment B raw3840 raw3840Labels = mixedMoment B raw3840step0 raw3840step0Labels := by
      have ha : raw3840step0 = (fun i j => raw3840 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3840step0 raw3840; decide +kernel
      have hl : raw3840step0Labels = raw3840Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3840 raw3840Labels permutation184 permutation2
    _ = mixedMoment B node2083 node2083Labels := by rfl

def raw3841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3841 raw3841Labels = mixedMoment B node2083 node2083Labels := by
  calc
    mixedMoment B raw3841 raw3841Labels = mixedMoment B raw3841step0 raw3841step0Labels := by
      have ha : raw3841step0 = (fun i j => raw3841 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3841step0 raw3841; decide +kernel
      have hl : raw3841step0Labels = raw3841Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3841 raw3841Labels permutation208 permutation2
    _ = mixedMoment B node2083 node2083Labels := by rfl

def raw3842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3842 raw3842Labels = mixedMoment B node2083 node2083Labels := by
  calc
    mixedMoment B raw3842 raw3842Labels = mixedMoment B raw3842step0 raw3842step0Labels := by
      have ha : raw3842step0 = (fun i j => raw3842 (permutation232 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3842step0 raw3842; decide +kernel
      have hl : raw3842step0Labels = raw3842Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3842 raw3842Labels permutation232 permutation2
    _ = mixedMoment B node2083 node2083Labels := by rfl

def raw3843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw3843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3843 raw3843Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw3843 raw3843Labels = mixedMoment B raw3843step0 raw3843step0Labels := by
      have ha : raw3843step0 = (fun i j => raw3843 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3843step0 raw3843; decide +kernel
      have hl : raw3843step0Labels = raw3843Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3843 raw3843Labels permutation184 permutation2
    _ = mixedMoment B node2233 node2233Labels := by rfl

def raw3844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3844 raw3844Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw3844 raw3844Labels = mixedMoment B raw3844step0 raw3844step0Labels := by
      have ha : raw3844step0 = (fun i j => raw3844 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3844step0 raw3844; decide +kernel
      have hl : raw3844step0Labels = raw3844Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3844 raw3844Labels permutation160 permutation2
    _ = mixedMoment B node2010 node2010Labels := by rfl

def raw3845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3845 raw3845Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw3845 raw3845Labels = mixedMoment B raw3845step0 raw3845step0Labels := by
      have ha : raw3845step0 = (fun i j => raw3845 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3845step0 raw3845; decide +kernel
      have hl : raw3845step0Labels = raw3845Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3845 raw3845Labels permutation154 permutation2
    _ = mixedMoment B node2010 node2010Labels := by rfl

def raw3846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3846 raw3846Labels = mixedMoment B node2010 node2010Labels := by
  calc
    _ = mixedMoment B node2010 node2010Labels := by rfl

def raw3847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3847 raw3847Labels = mixedMoment B node1457 node1457Labels := by
  calc
    mixedMoment B raw3847 raw3847Labels = mixedMoment B raw3847step0 raw3847step0Labels := by
      have ha : raw3847step0 = (fun i j => raw3847 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3847step0 raw3847; decide +kernel
      have hl : raw3847step0Labels = raw3847Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3847 raw3847Labels permutation590 permutation4
    _ = mixedMoment B node1457 node1457Labels := by rfl

def raw3848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3848 raw3848Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw3848 raw3848Labels = mixedMoment B raw3848step0 raw3848step0Labels := by
      have hz : ∀ j, raw3848 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3848step0 = (fun i j => raw3848 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3848step0 raw3848; decide +kernel
      have hl : raw3848step0Labels = raw3848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3848 raw3848Labels permutation265 hz
    mixedMoment B raw3848step0 raw3848step0Labels = mixedMoment B raw3848step1 raw3848step1Labels := by
      have ha : raw3848step1 = (fun i j => raw3848step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3848step1 raw3848step0; decide +kernel
      have hl : raw3848step1Labels = raw3848step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3848step0 raw3848step0Labels permutation40 permutation2
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw3849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3849 raw3849Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw3849 raw3849Labels = mixedMoment B raw3849step0 raw3849step0Labels := by
      have hz : ∀ j, raw3849 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3849step0 = (fun i j => raw3849 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3849step0 raw3849; decide +kernel
      have hl : raw3849step0Labels = raw3849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3849 raw3849Labels permutation265 hz
    mixedMoment B raw3849step0 raw3849step0Labels = mixedMoment B raw3849step1 raw3849step1Labels := by
      have ha : raw3849step1 = (fun i j => raw3849step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3849step1 raw3849step0; decide +kernel
      have hl : raw3849step1Labels = raw3849step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3849step0 raw3849step0Labels permutation46 permutation2
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw3850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3850 raw3850Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw3850 raw3850Labels = mixedMoment B raw3850step0 raw3850step0Labels := by
      have hz : ∀ j, raw3850 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3850step0 = (fun i j => raw3850 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3850step0 raw3850; decide +kernel
      have hl : raw3850step0Labels = raw3850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3850 raw3850Labels permutation265 hz
    mixedMoment B raw3850step0 raw3850step0Labels = mixedMoment B raw3850step1 raw3850step1Labels := by
      have ha : raw3850step1 = (fun i j => raw3850step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3850step1 raw3850step0; decide +kernel
      have hl : raw3850step1Labels = raw3850step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3850step0 raw3850step0Labels permutation40 permutation2
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw3851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3851 raw3851Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw3851 raw3851Labels = mixedMoment B raw3851step0 raw3851step0Labels := by
      have hz : ∀ j, raw3851 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3851step0 = (fun i j => raw3851 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3851step0 raw3851; decide +kernel
      have hl : raw3851step0Labels = raw3851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3851 raw3851Labels permutation265 hz
    mixedMoment B raw3851step0 raw3851step0Labels = mixedMoment B raw3851step1 raw3851step1Labels := by
      have ha : raw3851step1 = (fun i j => raw3851step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3851step1 raw3851step0; decide +kernel
      have hl : raw3851step1Labels = raw3851step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3851step0 raw3851step0Labels permutation34 permutation2
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw3852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3852 raw3852Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw3852 raw3852Labels = mixedMoment B raw3852step0 raw3852step0Labels := by
      have hz : ∀ j, raw3852 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3852step0 = (fun i j => raw3852 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3852step0 raw3852; decide +kernel
      have hl : raw3852step0Labels = raw3852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3852 raw3852Labels permutation265 hz
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw3853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3853 raw3853Labels = mixedMoment B node1460 node1460Labels := by
  calc
    mixedMoment B raw3853 raw3853Labels = mixedMoment B raw3853step0 raw3853step0Labels := by
      have hz : ∀ j, raw3853 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3853step0 = (fun i j => raw3853 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3853step0 raw3853; decide +kernel
      have hl : raw3853step0Labels = raw3853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3853 raw3853Labels permutation265 hz
    mixedMoment B raw3853step0 raw3853step0Labels = mixedMoment B raw3853step1 raw3853step1Labels := by
      have ha : raw3853step1 = (fun i j => raw3853step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3853step1 raw3853step0; decide +kernel
      have hl : raw3853step1Labels = raw3853step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3853step0 raw3853step0Labels permutation131 permutation4
    _ = mixedMoment B node1460 node1460Labels := by rfl

def raw3854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3854 raw3854Labels = mixedMoment B node1460 node1460Labels := by
  calc
    mixedMoment B raw3854 raw3854Labels = mixedMoment B raw3854step0 raw3854step0Labels := by
      have hz : ∀ j, raw3854 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3854step0 = (fun i j => raw3854 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3854step0 raw3854; decide +kernel
      have hl : raw3854step0Labels = raw3854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3854 raw3854Labels permutation265 hz
    mixedMoment B raw3854step0 raw3854step0Labels = mixedMoment B raw3854step1 raw3854step1Labels := by
      have ha : raw3854step1 = (fun i j => raw3854step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3854step1 raw3854step0; decide +kernel
      have hl : raw3854step1Labels = raw3854step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3854step0 raw3854step0Labels permutation129 permutation4
    _ = mixedMoment B node1460 node1460Labels := by rfl

def raw3855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw3855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw3855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3855 raw3855Labels = mixedMoment B node1460 node1460Labels := by
  calc
    mixedMoment B raw3855 raw3855Labels = mixedMoment B raw3855step0 raw3855step0Labels := by
      have hz : ∀ j, raw3855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3855step0 = (fun i j => raw3855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3855step0 raw3855; decide +kernel
      have hl : raw3855step0Labels = raw3855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3855 raw3855Labels permutation265 hz
    mixedMoment B raw3855step0 raw3855step0Labels = mixedMoment B raw3855step1 raw3855step1Labels := by
      have ha : raw3855step1 = (fun i j => raw3855step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3855step1 raw3855step0; decide +kernel
      have hl : raw3855step1Labels = raw3855step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3855step0 raw3855step0Labels permutation128 permutation4
    _ = mixedMoment B node1460 node1460Labels := by rfl

def raw3856 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3856 raw3856Labels = mixedMoment B node4830 node4830Labels := by
  calc
    mixedMoment B raw3856 raw3856Labels = mixedMoment B raw3856step0 raw3856step0Labels := by
      have ha : raw3856step0 = (fun i j => raw3856 (permutation609 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3856step0 raw3856; decide +kernel
      have hl : raw3856step0Labels = raw3856Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3856 raw3856Labels permutation609 permutation2
    _ = mixedMoment B node4830 node4830Labels := by rfl

def raw3857 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw3857step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3857step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3857step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3857step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3857step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3857 raw3857Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw3857 raw3857Labels = mixedMoment B raw3857step0 raw3857step0Labels := by
      have hz : ∀ j, raw3857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3857step0 = (fun i j => raw3857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3857step0 raw3857; decide +kernel
      have hl : raw3857step0Labels = raw3857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3857 raw3857Labels permutation434 hz
    mixedMoment B raw3857step0 raw3857step0Labels = mixedMoment B raw3857step1 raw3857step1Labels := by
      have hz : ∀ j, raw3857step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3857step1 = (fun i j => raw3857step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3857step1 raw3857step0; decide +kernel
      have hl : raw3857step1Labels = raw3857step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3857step0 raw3857step0Labels permutation56 hz
    mixedMoment B raw3857step1 raw3857step1Labels = mixedMoment B raw3857step2 raw3857step2Labels := by
      have ha : raw3857step2 = (fun i j => raw3857step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3857step2 raw3857step1; decide +kernel
      have hl : raw3857step2Labels = raw3857step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3857step1 raw3857step1Labels permutation29 permutation7
    mixedMoment B raw3857step2 raw3857step2Labels = mixedMoment B raw3857step3 raw3857step3Labels := by
      have ha : raw3857step3 = -raw3857step2 := by apply Matrix.ext; change ∀ i j, raw3857step3 i j = -(raw3857step2 i j); unfold raw3857step3 raw3857step2; decide +kernel
      have hl : raw3857step3Labels = raw3857step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3857step3 raw3857step3Labels = mixedMoment B raw3857step4 raw3857step4Labels := by
      have ha : raw3857step4 = raw3857step3 := by apply Matrix.ext; unfold raw3857step4 raw3857step3; decide +kernel
      have hl : raw3857step3Labels = labelEmbedding10 ∘ raw3857step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3857step3 raw3857step3Labels raw3857step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw3858 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3858step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw3858step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3858step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3858step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3858step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3858step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3858 raw3858Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw3858 raw3858Labels = mixedMoment B raw3858step0 raw3858step0Labels := by
      have hz : ∀ j, raw3858 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3858step0 = (fun i j => raw3858 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3858step0 raw3858; decide +kernel
      have hl : raw3858step0Labels = raw3858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3858 raw3858Labels permutation520 hz
    mixedMoment B raw3858step0 raw3858step0Labels = mixedMoment B raw3858step1 raw3858step1Labels := by
      have hz : ∀ j, raw3858step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3858step1 = (fun i j => raw3858step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3858step1 raw3858step0; decide +kernel
      have hl : raw3858step1Labels = raw3858step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3858step0 raw3858step0Labels permutation56 hz
    mixedMoment B raw3858step1 raw3858step1Labels = mixedMoment B raw3858step2 raw3858step2Labels := by
      have ha : raw3858step2 = (fun i j => raw3858step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3858step2 raw3858step1; decide +kernel
      have hl : raw3858step2Labels = raw3858step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3858step1 raw3858step1Labels permutation29 permutation7
    mixedMoment B raw3858step2 raw3858step2Labels = mixedMoment B raw3858step3 raw3858step3Labels := by
      have ha : raw3858step3 = -raw3858step2 := by apply Matrix.ext; change ∀ i j, raw3858step3 i j = -(raw3858step2 i j); unfold raw3858step3 raw3858step2; decide +kernel
      have hl : raw3858step3Labels = raw3858step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3858step3 raw3858step3Labels = mixedMoment B raw3858step4 raw3858step4Labels := by
      have ha : raw3858step4 = raw3858step3 := by apply Matrix.ext; unfold raw3858step4 raw3858step3; decide +kernel
      have hl : raw3858step3Labels = labelEmbedding10 ∘ raw3858step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3858step3 raw3858step3Labels raw3858step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw3859 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3859 raw3859Labels = mixedMoment B node4494 node4494Labels := by
  calc
    mixedMoment B raw3859 raw3859Labels = mixedMoment B raw3859step0 raw3859step0Labels := by
      have hz : ∀ j, raw3859 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3859step0 = (fun i j => raw3859 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3859step0 raw3859; decide +kernel
      have hl : raw3859step0Labels = raw3859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3859 raw3859Labels permutation265 hz
    mixedMoment B raw3859step0 raw3859step0Labels = mixedMoment B raw3859step1 raw3859step1Labels := by
      have ha : raw3859step1 = (fun i j => raw3859step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3859step1 raw3859step0; decide +kernel
      have hl : raw3859step1Labels = raw3859step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3859step0 raw3859step0Labels permutation137 permutation2
    _ = mixedMoment B node4494 node4494Labels := by rfl

def raw3860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw3860step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3860step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3860step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3860 raw3860Labels = mixedMoment B node4482 node4482Labels := by
  calc
    mixedMoment B raw3860 raw3860Labels = mixedMoment B raw3860step0 raw3860step0Labels := by
      have ha : raw3860step0 = (fun i j => raw3860 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3860step0 raw3860; decide +kernel
      have hl : raw3860step0Labels = raw3860Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3860 raw3860Labels permutation246 permutation4
    mixedMoment B raw3860step0 raw3860step0Labels = mixedMoment B raw3860step1 raw3860step1Labels := by
      have ha : raw3860step1 = -raw3860step0 := by apply Matrix.ext; change ∀ i j, raw3860step1 i j = -(raw3860step0 i j); unfold raw3860step1 raw3860step0; decide +kernel
      have hl : raw3860step1Labels = raw3860step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3860step1 raw3860step1Labels = mixedMoment B raw3860step2 raw3860step2Labels := by
      have ha : raw3860step2 = raw3860step1 := by apply Matrix.ext; unfold raw3860step2 raw3860step1; decide +kernel
      have hl : raw3860step1Labels = labelEmbedding7 ∘ raw3860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3860step1 raw3860step1Labels raw3860step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4482 node4482Labels := by rfl

def raw3861 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3861step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3861 raw3861Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw3861 raw3861Labels = mixedMoment B raw3861step0 raw3861step0Labels := by
      have hz : ∀ j, raw3861 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3861step0 = (fun i j => raw3861 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3861step0 raw3861; decide +kernel
      have hl : raw3861step0Labels = raw3861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3861 raw3861Labels permutation434 hz
    mixedMoment B raw3861step0 raw3861step0Labels = mixedMoment B raw3861step1 raw3861step1Labels := by
      have ha : raw3861step1 = (fun i j => raw3861step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3861step1 raw3861step0; decide +kernel
      have hl : raw3861step1Labels = raw3861step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3861step0 raw3861step0Labels permutation32 permutation6
    mixedMoment B raw3861step1 raw3861step1Labels = mixedMoment B raw3861step2 raw3861step2Labels := by
      have ha : raw3861step2 = raw3861step1 := by apply Matrix.ext; unfold raw3861step2 raw3861step1; decide +kernel
      have hl : raw3861step1Labels = labelEmbedding9 ∘ raw3861step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3861step1 raw3861step1Labels raw3861step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4886 node4886Labels := by rfl

def raw3862 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3862step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3862 raw3862Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw3862 raw3862Labels = mixedMoment B raw3862step0 raw3862step0Labels := by
      have hz : ∀ j, raw3862 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3862step0 = (fun i j => raw3862 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3862step0 raw3862; decide +kernel
      have hl : raw3862step0Labels = raw3862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3862 raw3862Labels permutation520 hz
    mixedMoment B raw3862step0 raw3862step0Labels = mixedMoment B raw3862step1 raw3862step1Labels := by
      have ha : raw3862step1 = (fun i j => raw3862step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3862step1 raw3862step0; decide +kernel
      have hl : raw3862step1Labels = raw3862step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3862step0 raw3862step0Labels permutation32 permutation6
    mixedMoment B raw3862step1 raw3862step1Labels = mixedMoment B raw3862step2 raw3862step2Labels := by
      have ha : raw3862step2 = raw3862step1 := by apply Matrix.ext; unfold raw3862step2 raw3862step1; decide +kernel
      have hl : raw3862step1Labels = labelEmbedding9 ∘ raw3862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3862step1 raw3862step1Labels raw3862step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4886 node4886Labels := by rfl

def raw3863 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3863 raw3863Labels = mixedMoment B node4482 node4482Labels := by
  calc
    mixedMoment B raw3863 raw3863Labels = mixedMoment B raw3863step0 raw3863step0Labels := by
      have ha : raw3863step0 = (fun i j => raw3863 (permutation590 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3863step0 raw3863; decide +kernel
      have hl : raw3863step0Labels = raw3863Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3863 raw3863Labels permutation590 permutation2
    _ = mixedMoment B node4482 node4482Labels := by rfl

def raw3864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw3864step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3864step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3864step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3864step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3864 raw3864Labels = mixedMoment B node4483 node4483Labels := by
  calc
    mixedMoment B raw3864 raw3864Labels = mixedMoment B raw3864step0 raw3864step0Labels := by
      have hz : ∀ j, raw3864 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3864step0 = (fun i j => raw3864 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3864step0 raw3864; decide +kernel
      have hl : raw3864step0Labels = raw3864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3864 raw3864Labels permutation265 hz
    mixedMoment B raw3864step0 raw3864step0Labels = mixedMoment B raw3864step1 raw3864step1Labels := by
      have ha : raw3864step1 = (fun i j => raw3864step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3864step1 raw3864step0; decide +kernel
      have hl : raw3864step1Labels = raw3864step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3864step0 raw3864step0Labels permutation53 permutation4
    mixedMoment B raw3864step1 raw3864step1Labels = mixedMoment B raw3864step2 raw3864step2Labels := by
      have ha : raw3864step2 = -raw3864step1 := by apply Matrix.ext; change ∀ i j, raw3864step2 i j = -(raw3864step1 i j); unfold raw3864step2 raw3864step1; decide +kernel
      have hl : raw3864step2Labels = raw3864step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3864step2 raw3864step2Labels = mixedMoment B raw3864step3 raw3864step3Labels := by
      have ha : raw3864step3 = raw3864step2 := by apply Matrix.ext; unfold raw3864step3 raw3864step2; decide +kernel
      have hl : raw3864step2Labels = labelEmbedding7 ∘ raw3864step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3864step2 raw3864step2Labels raw3864step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4483 node4483Labels := by rfl

def raw3865 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3865 raw3865Labels = mixedMoment B node4822 node4822Labels := by
  calc
    mixedMoment B raw3865 raw3865Labels = mixedMoment B raw3865step0 raw3865step0Labels := by
      have ha : raw3865step0 = (fun i j => raw3865 (permutation605 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3865step0 raw3865; decide +kernel
      have hl : raw3865step0Labels = raw3865Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3865 raw3865Labels permutation605 permutation2
    _ = mixedMoment B node4822 node4822Labels := by rfl

def raw3866 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3866step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3866step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3866step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3866 raw3866Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw3866 raw3866Labels = mixedMoment B raw3866step0 raw3866step0Labels := by
      have hz : ∀ j, raw3866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3866step0 = (fun i j => raw3866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3866step0 raw3866; decide +kernel
      have hl : raw3866step0Labels = raw3866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3866 raw3866Labels permutation434 hz
    mixedMoment B raw3866step0 raw3866step0Labels = mixedMoment B raw3866step1 raw3866step1Labels := by
      have hz : ∀ j, raw3866step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3866step1 = (fun i j => raw3866step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3866step1 raw3866step0; decide +kernel
      have hl : raw3866step1Labels = raw3866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3866step0 raw3866step0Labels permutation56 hz
    mixedMoment B raw3866step1 raw3866step1Labels = mixedMoment B raw3866step2 raw3866step2Labels := by
      have ha : raw3866step2 = (fun i j => raw3866step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3866step2 raw3866step1; decide +kernel
      have hl : raw3866step2Labels = raw3866step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3866step1 raw3866step1Labels permutation10 permutation6
    mixedMoment B raw3866step2 raw3866step2Labels = mixedMoment B raw3866step3 raw3866step3Labels := by
      have ha : raw3866step3 = raw3866step2 := by apply Matrix.ext; unfold raw3866step3 raw3866step2; decide +kernel
      have hl : raw3866step2Labels = labelEmbedding9 ∘ raw3866step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3866step2 raw3866step2Labels raw3866step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw3867 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3867step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3867step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3867step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3867step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3867step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3867 raw3867Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw3867 raw3867Labels = mixedMoment B raw3867step0 raw3867step0Labels := by
      have hz : ∀ j, raw3867 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3867step0 = (fun i j => raw3867 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3867step0 raw3867; decide +kernel
      have hl : raw3867step0Labels = raw3867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3867 raw3867Labels permutation520 hz
    mixedMoment B raw3867step0 raw3867step0Labels = mixedMoment B raw3867step1 raw3867step1Labels := by
      have hz : ∀ j, raw3867step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3867step1 = (fun i j => raw3867step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3867step1 raw3867step0; decide +kernel
      have hl : raw3867step1Labels = raw3867step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3867step0 raw3867step0Labels permutation56 hz
    mixedMoment B raw3867step1 raw3867step1Labels = mixedMoment B raw3867step2 raw3867step2Labels := by
      have ha : raw3867step2 = (fun i j => raw3867step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3867step2 raw3867step1; decide +kernel
      have hl : raw3867step2Labels = raw3867step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3867step1 raw3867step1Labels permutation10 permutation6
    mixedMoment B raw3867step2 raw3867step2Labels = mixedMoment B raw3867step3 raw3867step3Labels := by
      have ha : raw3867step3 = raw3867step2 := by apply Matrix.ext; unfold raw3867step3 raw3867step2; decide +kernel
      have hl : raw3867step2Labels = labelEmbedding9 ∘ raw3867step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3867step2 raw3867step2Labels raw3867step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw3868 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3868 raw3868Labels = mixedMoment B node4483 node4483Labels := by
  calc
    mixedMoment B raw3868 raw3868Labels = mixedMoment B raw3868step0 raw3868step0Labels := by
      have hz : ∀ j, raw3868 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3868step0 = (fun i j => raw3868 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3868step0 raw3868; decide +kernel
      have hl : raw3868step0Labels = raw3868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3868 raw3868Labels permutation265 hz
    mixedMoment B raw3868step0 raw3868step0Labels = mixedMoment B raw3868step1 raw3868step1Labels := by
      have ha : raw3868step1 = (fun i j => raw3868step0 (permutation131 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3868step1 raw3868step0; decide +kernel
      have hl : raw3868step1Labels = raw3868step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3868step0 raw3868step0Labels permutation131 permutation2
    _ = mixedMoment B node4483 node4483Labels := by rfl

def raw3869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw3869step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3869step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3869step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3869step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3869 raw3869Labels = mixedMoment B node4483 node4483Labels := by
  calc
    mixedMoment B raw3869 raw3869Labels = mixedMoment B raw3869step0 raw3869step0Labels := by
      have hz : ∀ j, raw3869 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3869step0 = (fun i j => raw3869 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3869step0 raw3869; decide +kernel
      have hl : raw3869step0Labels = raw3869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3869 raw3869Labels permutation265 hz
    mixedMoment B raw3869step0 raw3869step0Labels = mixedMoment B raw3869step1 raw3869step1Labels := by
      have ha : raw3869step1 = (fun i j => raw3869step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3869step1 raw3869step0; decide +kernel
      have hl : raw3869step1Labels = raw3869step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3869step0 raw3869step0Labels permutation51 permutation4
    mixedMoment B raw3869step1 raw3869step1Labels = mixedMoment B raw3869step2 raw3869step2Labels := by
      have ha : raw3869step2 = -raw3869step1 := by apply Matrix.ext; change ∀ i j, raw3869step2 i j = -(raw3869step1 i j); unfold raw3869step2 raw3869step1; decide +kernel
      have hl : raw3869step2Labels = raw3869step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3869step2 raw3869step2Labels = mixedMoment B raw3869step3 raw3869step3Labels := by
      have ha : raw3869step3 = raw3869step2 := by apply Matrix.ext; unfold raw3869step3 raw3869step2; decide +kernel
      have hl : raw3869step2Labels = labelEmbedding7 ∘ raw3869step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3869step2 raw3869step2Labels raw3869step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4483 node4483Labels := by rfl

def raw3870 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3870 raw3870Labels = mixedMoment B node4822 node4822Labels := by
  calc
    mixedMoment B raw3870 raw3870Labels = mixedMoment B raw3870step0 raw3870step0Labels := by
      have ha : raw3870step0 = (fun i j => raw3870 (permutation603 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3870step0 raw3870; decide +kernel
      have hl : raw3870step0Labels = raw3870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3870 raw3870Labels permutation603 permutation2
    _ = mixedMoment B node4822 node4822Labels := by rfl

def raw3871 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3871step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3871step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3871step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3871 raw3871Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw3871 raw3871Labels = mixedMoment B raw3871step0 raw3871step0Labels := by
      have hz : ∀ j, raw3871 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3871step0 = (fun i j => raw3871 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3871step0 raw3871; decide +kernel
      have hl : raw3871step0Labels = raw3871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3871 raw3871Labels permutation520 hz
    mixedMoment B raw3871step0 raw3871step0Labels = mixedMoment B raw3871step1 raw3871step1Labels := by
      have hz : ∀ j, raw3871step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3871step1 = (fun i j => raw3871step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3871step1 raw3871step0; decide +kernel
      have hl : raw3871step1Labels = raw3871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3871step0 raw3871step0Labels permutation56 hz
    mixedMoment B raw3871step1 raw3871step1Labels = mixedMoment B raw3871step2 raw3871step2Labels := by
      have ha : raw3871step2 = (fun i j => raw3871step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3871step2 raw3871step1; decide +kernel
      have hl : raw3871step2Labels = raw3871step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3871step1 raw3871step1Labels permutation8 permutation6
    mixedMoment B raw3871step2 raw3871step2Labels = mixedMoment B raw3871step3 raw3871step3Labels := by
      have ha : raw3871step3 = raw3871step2 := by apply Matrix.ext; unfold raw3871step3 raw3871step2; decide +kernel
      have hl : raw3871step2Labels = labelEmbedding9 ∘ raw3871step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3871step2 raw3871step2Labels raw3871step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw3872 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3872 raw3872Labels = mixedMoment B node4483 node4483Labels := by
  calc
    mixedMoment B raw3872 raw3872Labels = mixedMoment B raw3872step0 raw3872step0Labels := by
      have hz : ∀ j, raw3872 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3872step0 = (fun i j => raw3872 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3872step0 raw3872; decide +kernel
      have hl : raw3872step0Labels = raw3872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3872 raw3872Labels permutation265 hz
    mixedMoment B raw3872step0 raw3872step0Labels = mixedMoment B raw3872step1 raw3872step1Labels := by
      have ha : raw3872step1 = (fun i j => raw3872step0 (permutation129 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3872step1 raw3872step0; decide +kernel
      have hl : raw3872step1Labels = raw3872step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3872step0 raw3872step0Labels permutation129 permutation2
    _ = mixedMoment B node4483 node4483Labels := by rfl

def raw3873 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3873step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3873step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3873step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3873 raw3873Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw3873 raw3873Labels = mixedMoment B raw3873step0 raw3873step0Labels := by
      have hz : ∀ j, raw3873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3873step0 = (fun i j => raw3873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3873step0 raw3873; decide +kernel
      have hl : raw3873step0Labels = raw3873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3873 raw3873Labels permutation346 hz
    mixedMoment B raw3873step0 raw3873step0Labels = mixedMoment B raw3873step1 raw3873step1Labels := by
      have hz : ∀ j, raw3873step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3873step1 = (fun i j => raw3873step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3873step1 raw3873step0; decide +kernel
      have hl : raw3873step1Labels = raw3873step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3873step0 raw3873step0Labels permutation56 hz
    mixedMoment B raw3873step1 raw3873step1Labels = mixedMoment B raw3873step2 raw3873step2Labels := by
      have ha : raw3873step2 = (fun i j => raw3873step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3873step2 raw3873step1; decide +kernel
      have hl : raw3873step2Labels = raw3873step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3873step1 raw3873step1Labels permutation8 permutation6
    mixedMoment B raw3873step2 raw3873step2Labels = mixedMoment B raw3873step3 raw3873step3Labels := by
      have ha : raw3873step3 = raw3873step2 := by apply Matrix.ext; unfold raw3873step3 raw3873step2; decide +kernel
      have hl : raw3873step2Labels = labelEmbedding9 ∘ raw3873step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3873step2 raw3873step2Labels raw3873step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw3874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw3874step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3874step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3874step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3874step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3874 raw3874Labels = mixedMoment B node4494 node4494Labels := by
  calc
    mixedMoment B raw3874 raw3874Labels = mixedMoment B raw3874step0 raw3874step0Labels := by
      have hz : ∀ j, raw3874 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3874step0 = (fun i j => raw3874 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3874step0 raw3874; decide +kernel
      have hl : raw3874step0Labels = raw3874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3874 raw3874Labels permutation265 hz
    mixedMoment B raw3874step0 raw3874step0Labels = mixedMoment B raw3874step1 raw3874step1Labels := by
      have ha : raw3874step1 = (fun i j => raw3874step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3874step1 raw3874step0; decide +kernel
      have hl : raw3874step1Labels = raw3874step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3874step0 raw3874step0Labels permutation32 permutation4
    mixedMoment B raw3874step1 raw3874step1Labels = mixedMoment B raw3874step2 raw3874step2Labels := by
      have ha : raw3874step2 = -raw3874step1 := by apply Matrix.ext; change ∀ i j, raw3874step2 i j = -(raw3874step1 i j); unfold raw3874step2 raw3874step1; decide +kernel
      have hl : raw3874step2Labels = raw3874step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3874step2 raw3874step2Labels = mixedMoment B raw3874step3 raw3874step3Labels := by
      have ha : raw3874step3 = raw3874step2 := by apply Matrix.ext; unfold raw3874step3 raw3874step2; decide +kernel
      have hl : raw3874step2Labels = labelEmbedding7 ∘ raw3874step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3874step2 raw3874step2Labels raw3874step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4494 node4494Labels := by rfl

def raw3875 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw3875step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3875step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3875step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3875 raw3875Labels = mixedMoment B node4830 node4830Labels := by
  calc
    mixedMoment B raw3875 raw3875Labels = mixedMoment B raw3875step0 raw3875step0Labels := by
      have ha : raw3875step0 = (fun i j => raw3875 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3875step0 raw3875; decide +kernel
      have hl : raw3875step0Labels = raw3875Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3875 raw3875Labels permutation152 permutation4
    mixedMoment B raw3875step0 raw3875step0Labels = mixedMoment B raw3875step1 raw3875step1Labels := by
      have ha : raw3875step1 = -raw3875step0 := by apply Matrix.ext; change ∀ i j, raw3875step1 i j = -(raw3875step0 i j); unfold raw3875step1 raw3875step0; decide +kernel
      have hl : raw3875step1Labels = raw3875step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3875step1 raw3875step1Labels = mixedMoment B raw3875step2 raw3875step2Labels := by
      have ha : raw3875step2 = raw3875step1 := by apply Matrix.ext; unfold raw3875step2 raw3875step1; decide +kernel
      have hl : raw3875step1Labels = labelEmbedding7 ∘ raw3875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3875step1 raw3875step1Labels raw3875step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4830 node4830Labels := by rfl

def raw3876 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3876step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3876step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3876step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3876step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3876 raw3876Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw3876 raw3876Labels = mixedMoment B raw3876step0 raw3876step0Labels := by
      have hz : ∀ j, raw3876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3876step0 = (fun i j => raw3876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3876step0 raw3876; decide +kernel
      have hl : raw3876step0Labels = raw3876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3876 raw3876Labels permutation434 hz
    mixedMoment B raw3876step0 raw3876step0Labels = mixedMoment B raw3876step1 raw3876step1Labels := by
      have hz : ∀ j, raw3876step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3876step1 = (fun i j => raw3876step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3876step1 raw3876step0; decide +kernel
      have hl : raw3876step1Labels = raw3876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3876step0 raw3876step0Labels permutation56 hz
    mixedMoment B raw3876step1 raw3876step1Labels = mixedMoment B raw3876step2 raw3876step2Labels := by
      have ha : raw3876step2 = (fun i j => raw3876step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3876step2 raw3876step1; decide +kernel
      have hl : raw3876step2Labels = raw3876step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3876step1 raw3876step1Labels permutation8 permutation6
    mixedMoment B raw3876step2 raw3876step2Labels = mixedMoment B raw3876step3 raw3876step3Labels := by
      have ha : raw3876step3 = raw3876step2 := by apply Matrix.ext; unfold raw3876step3 raw3876step2; decide +kernel
      have hl : raw3876step2Labels = labelEmbedding9 ∘ raw3876step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3876step2 raw3876step2Labels raw3876step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw3877 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw3877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3877step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3877step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3877step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3877 raw3877Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw3877 raw3877Labels = mixedMoment B raw3877step0 raw3877step0Labels := by
      have hz : ∀ j, raw3877 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3877step0 = (fun i j => raw3877 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3877step0 raw3877; decide +kernel
      have hl : raw3877step0Labels = raw3877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3877 raw3877Labels permutation520 hz
    mixedMoment B raw3877step0 raw3877step0Labels = mixedMoment B raw3877step1 raw3877step1Labels := by
      have hz : ∀ j, raw3877step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3877step1 = (fun i j => raw3877step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3877step1 raw3877step0; decide +kernel
      have hl : raw3877step1Labels = raw3877step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3877step0 raw3877step0Labels permutation56 hz
    mixedMoment B raw3877step1 raw3877step1Labels = mixedMoment B raw3877step2 raw3877step2Labels := by
      have ha : raw3877step2 = (fun i j => raw3877step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3877step2 raw3877step1; decide +kernel
      have hl : raw3877step2Labels = raw3877step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3877step1 raw3877step1Labels permutation8 permutation6
    mixedMoment B raw3877step2 raw3877step2Labels = mixedMoment B raw3877step3 raw3877step3Labels := by
      have ha : raw3877step3 = raw3877step2 := by apply Matrix.ext; unfold raw3877step3 raw3877step2; decide +kernel
      have hl : raw3877step2Labels = labelEmbedding9 ∘ raw3877step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3877step2 raw3877step2Labels raw3877step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw3878 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3878 raw3878Labels = mixedMoment B node2707 node2707Labels := by
  calc
    mixedMoment B raw3878 raw3878Labels = mixedMoment B raw3878step0 raw3878step0Labels := by
      have ha : raw3878step0 = (fun i j => raw3878 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3878step0 raw3878; decide +kernel
      have hl : raw3878step0Labels = raw3878Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3878 raw3878Labels permutation152 permutation6
    _ = mixedMoment B node2707 node2707Labels := by rfl

def raw3879 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3879step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3879 raw3879Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw3879 raw3879Labels = mixedMoment B raw3879step0 raw3879step0Labels := by
      have hz : ∀ j, raw3879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3879step0 = (fun i j => raw3879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3879step0 raw3879; decide +kernel
      have hl : raw3879step0Labels = raw3879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3879 raw3879Labels permutation434 hz
    mixedMoment B raw3879step0 raw3879step0Labels = mixedMoment B raw3879step1 raw3879step1Labels := by
      have hz : ∀ j, raw3879step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3879step1 = (fun i j => raw3879step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3879step1 raw3879step0; decide +kernel
      have hl : raw3879step1Labels = raw3879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3879step0 raw3879step0Labels permutation56 hz
    mixedMoment B raw3879step1 raw3879step1Labels = mixedMoment B raw3879step2 raw3879step2Labels := by
      have ha : raw3879step2 = (fun i j => raw3879step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3879step2 raw3879step1; decide +kernel
      have hl : raw3879step2Labels = raw3879step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3879step1 raw3879step1Labels permutation8 permutation6
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw3880 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3880step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3880step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3880step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3880 raw3880Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw3880 raw3880Labels = mixedMoment B raw3880step0 raw3880step0Labels := by
      have hz : ∀ j, raw3880 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3880step0 = (fun i j => raw3880 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3880step0 raw3880; decide +kernel
      have hl : raw3880step0Labels = raw3880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3880 raw3880Labels permutation520 hz
    mixedMoment B raw3880step0 raw3880step0Labels = mixedMoment B raw3880step1 raw3880step1Labels := by
      have hz : ∀ j, raw3880step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3880step1 = (fun i j => raw3880step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3880step1 raw3880step0; decide +kernel
      have hl : raw3880step1Labels = raw3880step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3880step0 raw3880step0Labels permutation56 hz
    mixedMoment B raw3880step1 raw3880step1Labels = mixedMoment B raw3880step2 raw3880step2Labels := by
      have ha : raw3880step2 = (fun i j => raw3880step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3880step2 raw3880step1; decide +kernel
      have hl : raw3880step2Labels = raw3880step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3880step1 raw3880step1Labels permutation8 permutation6
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw3881 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3881 raw3881Labels = mixedMoment B node1435 node1435Labels := by
  calc
    mixedMoment B raw3881 raw3881Labels = mixedMoment B raw3881step0 raw3881step0Labels := by
      have hz : ∀ j, raw3881 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3881step0 = (fun i j => raw3881 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3881step0 raw3881; decide +kernel
      have hl : raw3881step0Labels = raw3881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3881 raw3881Labels permutation265 hz
    mixedMoment B raw3881step0 raw3881step0Labels = mixedMoment B raw3881step1 raw3881step1Labels := by
      have ha : raw3881step1 = (fun i j => raw3881step0 (permutation128 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3881step1 raw3881step0; decide +kernel
      have hl : raw3881step1Labels = raw3881step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3881step0 raw3881step0Labels permutation128 permutation3
    _ = mixedMoment B node1435 node1435Labels := by rfl

def raw3882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3882 raw3882Labels = mixedMoment B node1696 node1696Labels := by
  calc
    mixedMoment B raw3882 raw3882Labels = mixedMoment B raw3882step0 raw3882step0Labels := by
      have ha : raw3882step0 = (fun i j => raw3882 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3882step0 raw3882; decide +kernel
      have hl : raw3882step0Labels = raw3882Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3882 raw3882Labels permutation152 permutation6
    _ = mixedMoment B node1696 node1696Labels := by rfl

def raw3883 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3883 raw3883Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw3883 raw3883Labels = mixedMoment B raw3883step0 raw3883step0Labels := by
      have hz : ∀ j, raw3883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3883step0 = (fun i j => raw3883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3883step0 raw3883; decide +kernel
      have hl : raw3883step0Labels = raw3883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3883 raw3883Labels permutation434 hz
    mixedMoment B raw3883step0 raw3883step0Labels = mixedMoment B raw3883step1 raw3883step1Labels := by
      have ha : raw3883step1 = (fun i j => raw3883step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3883step1 raw3883step0; decide +kernel
      have hl : raw3883step1Labels = raw3883step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3883step0 raw3883step0Labels permutation32 permutation6
    _ = mixedMoment B node2235 node2235Labels := by rfl

def raw3884 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3884 raw3884Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw3884 raw3884Labels = mixedMoment B raw3884step0 raw3884step0Labels := by
      have hz : ∀ j, raw3884 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3884step0 = (fun i j => raw3884 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3884step0 raw3884; decide +kernel
      have hl : raw3884step0Labels = raw3884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3884 raw3884Labels permutation520 hz
    mixedMoment B raw3884step0 raw3884step0Labels = mixedMoment B raw3884step1 raw3884step1Labels := by
      have ha : raw3884step1 = (fun i j => raw3884step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3884step1 raw3884step0; decide +kernel
      have hl : raw3884step1Labels = raw3884step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3884step0 raw3884step0Labels permutation32 permutation6
    _ = mixedMoment B node2235 node2235Labels := by rfl

def raw3885 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3885 raw3885Labels = mixedMoment B node1350 node1350Labels := by
  calc
    mixedMoment B raw3885 raw3885Labels = mixedMoment B raw3885step0 raw3885step0Labels := by
      have ha : raw3885step0 = (fun i j => raw3885 (permutation590 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3885step0 raw3885; decide +kernel
      have hl : raw3885step0Labels = raw3885Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3885 raw3885Labels permutation590 permutation3
    _ = mixedMoment B node1350 node1350Labels := by rfl

def raw3886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3886step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3886 raw3886Labels = mixedMoment B node1702 node1702Labels := by
  calc
    mixedMoment B raw3886 raw3886Labels = mixedMoment B raw3886step0 raw3886step0Labels := by
      have hz : ∀ j, raw3886 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3886step0 = (fun i j => raw3886 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3886step0 raw3886; decide +kernel
      have hl : raw3886step0Labels = raw3886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3886 raw3886Labels permutation265 hz
    mixedMoment B raw3886step0 raw3886step0Labels = mixedMoment B raw3886step1 raw3886step1Labels := by
      have ha : raw3886step1 = (fun i j => raw3886step0 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3886step1 raw3886step0; decide +kernel
      have hl : raw3886step1Labels = raw3886step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3886step0 raw3886step0Labels permutation40 permutation6
    _ = mixedMoment B node1702 node1702Labels := by rfl

def raw3887 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3887 raw3887Labels = mixedMoment B node2188 node2188Labels := by
  calc
    mixedMoment B raw3887 raw3887Labels = mixedMoment B raw3887step0 raw3887step0Labels := by
      have ha : raw3887step0 = (fun i j => raw3887 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3887step0 raw3887; decide +kernel
      have hl : raw3887step0Labels = raw3887Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3887 raw3887Labels permutation160 permutation6
    _ = mixedMoment B node2188 node2188Labels := by rfl

def raw3888 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3888step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3888step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3888step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3888 raw3888Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw3888 raw3888Labels = mixedMoment B raw3888step0 raw3888step0Labels := by
      have hz : ∀ j, raw3888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3888step0 = (fun i j => raw3888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3888step0 raw3888; decide +kernel
      have hl : raw3888step0Labels = raw3888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3888 raw3888Labels permutation434 hz
    mixedMoment B raw3888step0 raw3888step0Labels = mixedMoment B raw3888step1 raw3888step1Labels := by
      have hz : ∀ j, raw3888step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3888step1 = (fun i j => raw3888step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3888step1 raw3888step0; decide +kernel
      have hl : raw3888step1Labels = raw3888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3888step0 raw3888step0Labels permutation56 hz
    mixedMoment B raw3888step1 raw3888step1Labels = mixedMoment B raw3888step2 raw3888step2Labels := by
      have ha : raw3888step2 = (fun i j => raw3888step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3888step2 raw3888step1; decide +kernel
      have hl : raw3888step2Labels = raw3888step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3888step1 raw3888step1Labels permutation10 permutation6
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw3889 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3889step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3889 raw3889Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw3889 raw3889Labels = mixedMoment B raw3889step0 raw3889step0Labels := by
      have hz : ∀ j, raw3889 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3889step0 = (fun i j => raw3889 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3889step0 raw3889; decide +kernel
      have hl : raw3889step0Labels = raw3889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3889 raw3889Labels permutation520 hz
    mixedMoment B raw3889step0 raw3889step0Labels = mixedMoment B raw3889step1 raw3889step1Labels := by
      have hz : ∀ j, raw3889step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3889step1 = (fun i j => raw3889step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3889step1 raw3889step0; decide +kernel
      have hl : raw3889step1Labels = raw3889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3889step0 raw3889step0Labels permutation56 hz
    mixedMoment B raw3889step1 raw3889step1Labels = mixedMoment B raw3889step2 raw3889step2Labels := by
      have ha : raw3889step2 = (fun i j => raw3889step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3889step2 raw3889step1; decide +kernel
      have hl : raw3889step2Labels = raw3889step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3889step1 raw3889step1Labels permutation10 permutation6
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw3890 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3890step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw3890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3890 raw3890Labels = mixedMoment B node1351 node1351Labels := by
  calc
    mixedMoment B raw3890 raw3890Labels = mixedMoment B raw3890step0 raw3890step0Labels := by
      have hz : ∀ j, raw3890 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3890step0 = (fun i j => raw3890 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3890step0 raw3890; decide +kernel
      have hl : raw3890step0Labels = raw3890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3890 raw3890Labels permutation265 hz
    mixedMoment B raw3890step0 raw3890step0Labels = mixedMoment B raw3890step1 raw3890step1Labels := by
      have ha : raw3890step1 = (fun i j => raw3890step0 (permutation131 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3890step1 raw3890step0; decide +kernel
      have hl : raw3890step1Labels = raw3890step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3890step0 raw3890step0Labels permutation131 permutation3
    _ = mixedMoment B node1351 node1351Labels := by rfl

def raw3891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3891Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3891step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3891 raw3891Labels = mixedMoment B node1702 node1702Labels := by
  calc
    mixedMoment B raw3891 raw3891Labels = mixedMoment B raw3891step0 raw3891step0Labels := by
      have hz : ∀ j, raw3891 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3891step0 = (fun i j => raw3891 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3891step0 raw3891; decide +kernel
      have hl : raw3891step0Labels = raw3891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3891 raw3891Labels permutation265 hz
    mixedMoment B raw3891step0 raw3891step0Labels = mixedMoment B raw3891step1 raw3891step1Labels := by
      have ha : raw3891step1 = (fun i j => raw3891step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3891step1 raw3891step0; decide +kernel
      have hl : raw3891step1Labels = raw3891step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3891step0 raw3891step0Labels permutation34 permutation6
    _ = mixedMoment B node1702 node1702Labels := by rfl

def raw3892 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3892Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3892 raw3892Labels = mixedMoment B node2188 node2188Labels := by
  calc
    mixedMoment B raw3892 raw3892Labels = mixedMoment B raw3892step0 raw3892step0Labels := by
      have ha : raw3892step0 = (fun i j => raw3892 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3892step0 raw3892; decide +kernel
      have hl : raw3892step0Labels = raw3892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3892 raw3892Labels permutation154 permutation6
    _ = mixedMoment B node2188 node2188Labels := by rfl

def raw3893 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3893Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3893step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3893step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3893 raw3893Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw3893 raw3893Labels = mixedMoment B raw3893step0 raw3893step0Labels := by
      have hz : ∀ j, raw3893 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3893step0 = (fun i j => raw3893 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3893step0 raw3893; decide +kernel
      have hl : raw3893step0Labels = raw3893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3893 raw3893Labels permutation520 hz
    mixedMoment B raw3893step0 raw3893step0Labels = mixedMoment B raw3893step1 raw3893step1Labels := by
      have hz : ∀ j, raw3893step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3893step1 = (fun i j => raw3893step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3893step1 raw3893step0; decide +kernel
      have hl : raw3893step1Labels = raw3893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3893step0 raw3893step0Labels permutation56 hz
    mixedMoment B raw3893step1 raw3893step1Labels = mixedMoment B raw3893step2 raw3893step2Labels := by
      have ha : raw3893step2 = (fun i j => raw3893step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3893step2 raw3893step1; decide +kernel
      have hl : raw3893step2Labels = raw3893step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3893step1 raw3893step1Labels permutation8 permutation6
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw3894 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3894Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3894step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw3894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3894 raw3894Labels = mixedMoment B node1351 node1351Labels := by
  calc
    mixedMoment B raw3894 raw3894Labels = mixedMoment B raw3894step0 raw3894step0Labels := by
      have hz : ∀ j, raw3894 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3894step0 = (fun i j => raw3894 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3894step0 raw3894; decide +kernel
      have hl : raw3894step0Labels = raw3894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3894 raw3894Labels permutation265 hz
    mixedMoment B raw3894step0 raw3894step0Labels = mixedMoment B raw3894step1 raw3894step1Labels := by
      have ha : raw3894step1 = (fun i j => raw3894step0 (permutation129 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3894step1 raw3894step0; decide +kernel
      have hl : raw3894step1Labels = raw3894step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3894step0 raw3894step0Labels permutation129 permutation3
    _ = mixedMoment B node1351 node1351Labels := by rfl

def raw3895 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3895step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3895step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3895 raw3895Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw3895 raw3895Labels = mixedMoment B raw3895step0 raw3895step0Labels := by
      have hz : ∀ j, raw3895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3895step0 = (fun i j => raw3895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3895step0 raw3895; decide +kernel
      have hl : raw3895step0Labels = raw3895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3895 raw3895Labels permutation346 hz
    mixedMoment B raw3895step0 raw3895step0Labels = mixedMoment B raw3895step1 raw3895step1Labels := by
      have hz : ∀ j, raw3895step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3895step1 = (fun i j => raw3895step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3895step1 raw3895step0; decide +kernel
      have hl : raw3895step1Labels = raw3895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3895step0 raw3895step0Labels permutation56 hz
    mixedMoment B raw3895step1 raw3895step1Labels = mixedMoment B raw3895step2 raw3895step2Labels := by
      have ha : raw3895step2 = (fun i j => raw3895step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3895step2 raw3895step1; decide +kernel
      have hl : raw3895step2Labels = raw3895step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3895step1 raw3895step1Labels permutation8 permutation6
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw3896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3896step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3896 raw3896Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw3896 raw3896Labels = mixedMoment B raw3896step0 raw3896step0Labels := by
      have hz : ∀ j, raw3896 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3896step0 = (fun i j => raw3896 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3896step0 raw3896; decide +kernel
      have hl : raw3896step0Labels = raw3896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3896 raw3896Labels permutation265 hz
    mixedMoment B raw3896step0 raw3896step0Labels = mixedMoment B raw3896step1 raw3896step1Labels := by
      have ha : raw3896step1 = (fun i j => raw3896step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3896step1 raw3896step0; decide +kernel
      have hl : raw3896step1Labels = raw3896step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3896step0 raw3896step0Labels permutation32 permutation6
    _ = mixedMoment B node1700 node1700Labels := by rfl

def raw3897 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3897 raw3897Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw3897 raw3897Labels = mixedMoment B raw3897step0 raw3897step0Labels := by
      have ha : raw3897step0 = (fun i j => raw3897 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3897step0 raw3897; decide +kernel
      have hl : raw3897step0Labels = raw3897Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3897 raw3897Labels permutation152 permutation6
    _ = mixedMoment B node2187 node2187Labels := by rfl

def raw3898 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3898step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3898step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3898 raw3898Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw3898 raw3898Labels = mixedMoment B raw3898step0 raw3898step0Labels := by
      have hz : ∀ j, raw3898 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3898step0 = (fun i j => raw3898 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3898step0 raw3898; decide +kernel
      have hl : raw3898step0Labels = raw3898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3898 raw3898Labels permutation434 hz
    mixedMoment B raw3898step0 raw3898step0Labels = mixedMoment B raw3898step1 raw3898step1Labels := by
      have hz : ∀ j, raw3898step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3898step1 = (fun i j => raw3898step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3898step1 raw3898step0; decide +kernel
      have hl : raw3898step1Labels = raw3898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3898step0 raw3898step0Labels permutation56 hz
    mixedMoment B raw3898step1 raw3898step1Labels = mixedMoment B raw3898step2 raw3898step2Labels := by
      have ha : raw3898step2 = (fun i j => raw3898step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3898step2 raw3898step1; decide +kernel
      have hl : raw3898step2Labels = raw3898step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3898step1 raw3898step1Labels permutation8 permutation6
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw3899 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw3899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3899step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3899step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3899 raw3899Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw3899 raw3899Labels = mixedMoment B raw3899step0 raw3899step0Labels := by
      have hz : ∀ j, raw3899 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3899step0 = (fun i j => raw3899 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3899step0 raw3899; decide +kernel
      have hl : raw3899step0Labels = raw3899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3899 raw3899Labels permutation520 hz
    mixedMoment B raw3899step0 raw3899step0Labels = mixedMoment B raw3899step1 raw3899step1Labels := by
      have hz : ∀ j, raw3899step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3899step1 = (fun i j => raw3899step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3899step1 raw3899step0; decide +kernel
      have hl : raw3899step1Labels = raw3899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3899step0 raw3899step0Labels permutation56 hz
    mixedMoment B raw3899step1 raw3899step1Labels = mixedMoment B raw3899step2 raw3899step2Labels := by
      have ha : raw3899step2 = (fun i j => raw3899step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3899step2 raw3899step1; decide +kernel
      have hl : raw3899step2Labels = raw3899step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3899step1 raw3899step1Labels permutation8 permutation6
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw3900 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3900 raw3900Labels = mixedMoment B node2283 node2283Labels := by
  calc
    mixedMoment B raw3900 raw3900Labels = mixedMoment B raw3900step0 raw3900step0Labels := by
      have hz : ∀ j, raw3900 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3900step0 = (fun i j => raw3900 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3900step0 raw3900; decide +kernel
      have hl : raw3900step0Labels = raw3900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3900 raw3900Labels permutation265 hz
    mixedMoment B raw3900step0 raw3900step0Labels = mixedMoment B raw3900step1 raw3900step1Labels := by
      have ha : raw3900step1 = (fun i j => raw3900step0 (permutation128 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3900step1 raw3900step0; decide +kernel
      have hl : raw3900step1Labels = raw3900step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3900step0 raw3900step0Labels permutation128 permutation2
    _ = mixedMoment B node2283 node2283Labels := by rfl

def raw3901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3901 raw3901Labels = mixedMoment B node2050 node2050Labels := by
  calc
    mixedMoment B raw3901 raw3901Labels = mixedMoment B raw3901step0 raw3901step0Labels := by
      have ha : raw3901step0 = (fun i j => raw3901 (permutation609 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3901step0 raw3901; decide +kernel
      have hl : raw3901step0Labels = raw3901Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3901 raw3901Labels permutation609 permutation2
    _ = mixedMoment B node2050 node2050Labels := by rfl

def raw3902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3902step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3902 raw3902Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw3902 raw3902Labels = mixedMoment B raw3902step0 raw3902step0Labels := by
      have hz : ∀ j, raw3902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3902step0 = (fun i j => raw3902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3902step0 raw3902; decide +kernel
      have hl : raw3902step0Labels = raw3902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3902 raw3902Labels permutation434 hz
    mixedMoment B raw3902step0 raw3902step0Labels = mixedMoment B raw3902step1 raw3902step1Labels := by
      have hz : ∀ j, raw3902step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3902step1 = (fun i j => raw3902step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3902step1 raw3902step0; decide +kernel
      have hl : raw3902step1Labels = raw3902step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3902step0 raw3902step0Labels permutation56 hz
    mixedMoment B raw3902step1 raw3902step1Labels = mixedMoment B raw3902step2 raw3902step2Labels := by
      have ha : raw3902step2 = (fun i j => raw3902step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3902step2 raw3902step1; decide +kernel
      have hl : raw3902step2Labels = raw3902step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3902step1 raw3902step1Labels permutation29 permutation2
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw3903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3903 raw3903Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw3903 raw3903Labels = mixedMoment B raw3903step0 raw3903step0Labels := by
      have hz : ∀ j, raw3903 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3903step0 = (fun i j => raw3903 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3903step0 raw3903; decide +kernel
      have hl : raw3903step0Labels = raw3903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3903 raw3903Labels permutation520 hz
    mixedMoment B raw3903step0 raw3903step0Labels = mixedMoment B raw3903step1 raw3903step1Labels := by
      have hz : ∀ j, raw3903step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3903step1 = (fun i j => raw3903step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3903step1 raw3903step0; decide +kernel
      have hl : raw3903step1Labels = raw3903step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3903step0 raw3903step0Labels permutation56 hz
    mixedMoment B raw3903step1 raw3903step1Labels = mixedMoment B raw3903step2 raw3903step2Labels := by
      have ha : raw3903step2 = (fun i j => raw3903step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3903step2 raw3903step1; decide +kernel
      have hl : raw3903step2Labels = raw3903step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3903step1 raw3903step1Labels permutation29 permutation2
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw3904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3904 raw3904Labels = mixedMoment B node1078 node1078Labels := by
  calc
    mixedMoment B raw3904 raw3904Labels = mixedMoment B raw3904step0 raw3904step0Labels := by
      have hz : ∀ j, raw3904 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3904step0 = (fun i j => raw3904 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3904step0 raw3904; decide +kernel
      have hl : raw3904step0Labels = raw3904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3904 raw3904Labels permutation265 hz
    mixedMoment B raw3904step0 raw3904step0Labels = mixedMoment B raw3904step1 raw3904step1Labels := by
      have ha : raw3904step1 = (fun i j => raw3904step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3904step1 raw3904step0; decide +kernel
      have hl : raw3904step1Labels = raw3904step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3904step0 raw3904step0Labels permutation137 permutation2
    _ = mixedMoment B node1078 node1078Labels := by rfl

def raw3905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw3905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3905 raw3905Labels = mixedMoment B node1065 node1065Labels := by
  calc
    mixedMoment B raw3905 raw3905Labels = mixedMoment B raw3905step0 raw3905step0Labels := by
      have ha : raw3905step0 = (fun i j => raw3905 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3905step0 raw3905; decide +kernel
      have hl : raw3905step0Labels = raw3905Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3905 raw3905Labels permutation246 permutation4
    mixedMoment B raw3905step0 raw3905step0Labels = mixedMoment B raw3905step1 raw3905step1Labels := by
      have ha : raw3905step1 = -raw3905step0 := by apply Matrix.ext; change ∀ i j, raw3905step1 i j = -(raw3905step0 i j); unfold raw3905step1 raw3905step0; decide +kernel
      have hl : raw3905step1Labels = raw3905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1065 node1065Labels := by rfl

def raw3906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw3906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3906 raw3906Labels = mixedMoment B node1066 node1066Labels := by
  calc
    mixedMoment B raw3906 raw3906Labels = mixedMoment B raw3906step0 raw3906step0Labels := by
      have hz : ∀ j, raw3906 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3906step0 = (fun i j => raw3906 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3906step0 raw3906; decide +kernel
      have hl : raw3906step0Labels = raw3906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3906 raw3906Labels permutation265 hz
    mixedMoment B raw3906step0 raw3906step0Labels = mixedMoment B raw3906step1 raw3906step1Labels := by
      have ha : raw3906step1 = (fun i j => raw3906step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3906step1 raw3906step0; decide +kernel
      have hl : raw3906step1Labels = raw3906step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3906step0 raw3906step0Labels permutation53 permutation4
    mixedMoment B raw3906step1 raw3906step1Labels = mixedMoment B raw3906step2 raw3906step2Labels := by
      have ha : raw3906step2 = -raw3906step1 := by apply Matrix.ext; change ∀ i j, raw3906step2 i j = -(raw3906step1 i j); unfold raw3906step2 raw3906step1; decide +kernel
      have hl : raw3906step2Labels = raw3906step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1066 node1066Labels := by rfl

def raw3907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw3907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3907 raw3907Labels = mixedMoment B node1066 node1066Labels := by
  calc
    mixedMoment B raw3907 raw3907Labels = mixedMoment B raw3907step0 raw3907step0Labels := by
      have hz : ∀ j, raw3907 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3907step0 = (fun i j => raw3907 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3907step0 raw3907; decide +kernel
      have hl : raw3907step0Labels = raw3907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3907 raw3907Labels permutation265 hz
    mixedMoment B raw3907step0 raw3907step0Labels = mixedMoment B raw3907step1 raw3907step1Labels := by
      have ha : raw3907step1 = (fun i j => raw3907step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3907step1 raw3907step0; decide +kernel
      have hl : raw3907step1Labels = raw3907step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3907step0 raw3907step0Labels permutation51 permutation4
    mixedMoment B raw3907step1 raw3907step1Labels = mixedMoment B raw3907step2 raw3907step2Labels := by
      have ha : raw3907step2 = -raw3907step1 := by apply Matrix.ext; change ∀ i j, raw3907step2 i j = -(raw3907step1 i j); unfold raw3907step2 raw3907step1; decide +kernel
      have hl : raw3907step2Labels = raw3907step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1066 node1066Labels := by rfl

def raw3908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw3908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3908 raw3908Labels = mixedMoment B node1078 node1078Labels := by
  calc
    mixedMoment B raw3908 raw3908Labels = mixedMoment B raw3908step0 raw3908step0Labels := by
      have hz : ∀ j, raw3908 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3908step0 = (fun i j => raw3908 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3908step0 raw3908; decide +kernel
      have hl : raw3908step0Labels = raw3908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3908 raw3908Labels permutation265 hz
    mixedMoment B raw3908step0 raw3908step0Labels = mixedMoment B raw3908step1 raw3908step1Labels := by
      have ha : raw3908step1 = (fun i j => raw3908step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3908step1 raw3908step0; decide +kernel
      have hl : raw3908step1Labels = raw3908step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3908step0 raw3908step0Labels permutation32 permutation4
    mixedMoment B raw3908step1 raw3908step1Labels = mixedMoment B raw3908step2 raw3908step2Labels := by
      have ha : raw3908step2 = -raw3908step1 := by apply Matrix.ext; change ∀ i j, raw3908step2 i j = -(raw3908step1 i j); unfold raw3908step2 raw3908step1; decide +kernel
      have hl : raw3908step2Labels = raw3908step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1078 node1078Labels := by rfl

def raw3909 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3909 raw3909Labels = mixedMoment B node2283 node2283Labels := by
  calc
    mixedMoment B raw3909 raw3909Labels = mixedMoment B raw3909step0 raw3909step0Labels := by
      have hz : ∀ j, raw3909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3909step0 = (fun i j => raw3909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3909step0 raw3909; decide +kernel
      have hl : raw3909step0Labels = raw3909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3909 raw3909Labels permutation434 hz
    mixedMoment B raw3909step0 raw3909step0Labels = mixedMoment B raw3909step1 raw3909step1Labels := by
      have ha : raw3909step1 = (fun i j => raw3909step0 (permutation128 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3909step1 raw3909step0; decide +kernel
      have hl : raw3909step1Labels = raw3909step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3909step0 raw3909step0Labels permutation128 permutation2
    _ = mixedMoment B node2283 node2283Labels := by rfl

def raw3910 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3910 raw3910Labels = mixedMoment B node2283 node2283Labels := by
  calc
    mixedMoment B raw3910 raw3910Labels = mixedMoment B raw3910step0 raw3910step0Labels := by
      have hz : ∀ j, raw3910 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3910step0 = (fun i j => raw3910 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3910step0 raw3910; decide +kernel
      have hl : raw3910step0Labels = raw3910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3910 raw3910Labels permutation520 hz
    mixedMoment B raw3910step0 raw3910step0Labels = mixedMoment B raw3910step1 raw3910step1Labels := by
      have ha : raw3910step1 = (fun i j => raw3910step0 (permutation128 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3910step1 raw3910step0; decide +kernel
      have hl : raw3910step1Labels = raw3910step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3910step0 raw3910step0Labels permutation128 permutation2
    _ = mixedMoment B node2283 node2283Labels := by rfl

def raw3911 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3911 raw3911Labels = mixedMoment B node1065 node1065Labels := by
  calc
    mixedMoment B raw3911 raw3911Labels = mixedMoment B raw3911step0 raw3911step0Labels := by
      have ha : raw3911step0 = (fun i j => raw3911 (permutation590 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3911step0 raw3911; decide +kernel
      have hl : raw3911step0Labels = raw3911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3911 raw3911Labels permutation590 permutation2
    _ = mixedMoment B node1065 node1065Labels := by rfl

def raw3912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![3, -2, -1]]
def raw3912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw3912step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3912step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3912step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3912step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3912step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3912 raw3912Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw3912 raw3912Labels = mixedMoment B raw3912step0 raw3912step0Labels := by
      have hz : ∀ j, raw3912 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3912step0 = (fun i j => raw3912 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3912step0 raw3912; decide +kernel
      have hl : raw3912step0Labels = raw3912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3912 raw3912Labels permutation434 hz
    mixedMoment B raw3912step0 raw3912step0Labels = mixedMoment B raw3912step1 raw3912step1Labels := by
      have hz : ∀ j, raw3912step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3912step1 = (fun i j => raw3912step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3912step1 raw3912step0; decide +kernel
      have hl : raw3912step1Labels = raw3912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3912step0 raw3912step0Labels permutation80 hz
    mixedMoment B raw3912step1 raw3912step1Labels = mixedMoment B raw3912step2 raw3912step2Labels := by
      have ha : raw3912step2 = (fun i j => raw3912step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3912step2 raw3912step1; decide +kernel
      have hl : raw3912step2Labels = raw3912step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3912step1 raw3912step1Labels permutation31 permutation3
    mixedMoment B raw3912step2 raw3912step2Labels = mixedMoment B raw3912step3 raw3912step3Labels := by
      have ha : raw3912step3 = -raw3912step2 := by apply Matrix.ext; change ∀ i j, raw3912step3 i j = -(raw3912step2 i j); unfold raw3912step3 raw3912step2; decide +kernel
      have hl : raw3912step3Labels = raw3912step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3912step3 raw3912step3Labels = mixedMoment B raw3912step4 raw3912step4Labels := by
      have ha : raw3912step4 = raw3912step3 := by apply Matrix.ext; unfold raw3912step4 raw3912step3; decide +kernel
      have hl : raw3912step3Labels = labelEmbedding6 ∘ raw3912step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3912step3 raw3912step3Labels raw3912step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw3913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw3913step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3913step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3913step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3913step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3913 raw3913Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw3913 raw3913Labels = mixedMoment B raw3913step0 raw3913step0Labels := by
      have hz : ∀ j, raw3913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3913step0 = (fun i j => raw3913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3913step0 raw3913; decide +kernel
      have hl : raw3913step0Labels = raw3913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3913 raw3913Labels permutation434 hz
    mixedMoment B raw3913step0 raw3913step0Labels = mixedMoment B raw3913step1 raw3913step1Labels := by
      have ha : raw3913step1 = (fun i j => raw3913step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3913step1 raw3913step0; decide +kernel
      have hl : raw3913step1Labels = raw3913step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3913step0 raw3913step0Labels permutation139 permutation3
    mixedMoment B raw3913step1 raw3913step1Labels = mixedMoment B raw3913step2 raw3913step2Labels := by
      have ha : raw3913step2 = -raw3913step1 := by apply Matrix.ext; change ∀ i j, raw3913step2 i j = -(raw3913step1 i j); unfold raw3913step2 raw3913step1; decide +kernel
      have hl : raw3913step2Labels = raw3913step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3913step2 raw3913step2Labels = mixedMoment B raw3913step3 raw3913step3Labels := by
      have ha : raw3913step3 = raw3913step2 := by apply Matrix.ext; unfold raw3913step3 raw3913step2; decide +kernel
      have hl : raw3913step2Labels = labelEmbedding6 ∘ raw3913step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3913step2 raw3913step2Labels raw3913step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw3914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw3914step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3914step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3914step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3914step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3914 raw3914Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw3914 raw3914Labels = mixedMoment B raw3914step0 raw3914step0Labels := by
      have hz : ∀ j, raw3914 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3914step0 = (fun i j => raw3914 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3914step0 raw3914; decide +kernel
      have hl : raw3914step0Labels = raw3914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3914 raw3914Labels permutation346 hz
    mixedMoment B raw3914step0 raw3914step0Labels = mixedMoment B raw3914step1 raw3914step1Labels := by
      have ha : raw3914step1 = (fun i j => raw3914step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3914step1 raw3914step0; decide +kernel
      have hl : raw3914step1Labels = raw3914step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3914step0 raw3914step0Labels permutation139 permutation3
    mixedMoment B raw3914step1 raw3914step1Labels = mixedMoment B raw3914step2 raw3914step2Labels := by
      have ha : raw3914step2 = -raw3914step1 := by apply Matrix.ext; change ∀ i j, raw3914step2 i j = -(raw3914step1 i j); unfold raw3914step2 raw3914step1; decide +kernel
      have hl : raw3914step2Labels = raw3914step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3914step2 raw3914step2Labels = mixedMoment B raw3914step3 raw3914step3Labels := by
      have ha : raw3914step3 = raw3914step2 := by apply Matrix.ext; unfold raw3914step3 raw3914step2; decide +kernel
      have hl : raw3914step2Labels = labelEmbedding6 ∘ raw3914step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3914step2 raw3914step2Labels raw3914step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw3915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw3915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw3915step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3915step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw3915step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3915step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw3915step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3915 raw3915Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw3915 raw3915Labels = mixedMoment B raw3915step0 raw3915step0Labels := by
      have hz : ∀ j, raw3915 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3915step0 = (fun i j => raw3915 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3915step0 raw3915; decide +kernel
      have hl : raw3915step0Labels = raw3915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3915 raw3915Labels permutation434 hz
    mixedMoment B raw3915step0 raw3915step0Labels = mixedMoment B raw3915step1 raw3915step1Labels := by
      have hz : ∀ j, raw3915step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3915step1 = (fun i j => raw3915step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3915step1 raw3915step0; decide +kernel
      have hl : raw3915step1Labels = raw3915step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3915step0 raw3915step0Labels permutation80 hz
    mixedMoment B raw3915step1 raw3915step1Labels = mixedMoment B raw3915step2 raw3915step2Labels := by
      have ha : raw3915step2 = (fun i j => raw3915step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3915step2 raw3915step1; decide +kernel
      have hl : raw3915step2Labels = raw3915step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3915step1 raw3915step1Labels permutation29 permutation3
    mixedMoment B raw3915step2 raw3915step2Labels = mixedMoment B raw3915step3 raw3915step3Labels := by
      have ha : raw3915step3 = -raw3915step2 := by apply Matrix.ext; change ∀ i j, raw3915step3 i j = -(raw3915step2 i j); unfold raw3915step3 raw3915step2; decide +kernel
      have hl : raw3915step3Labels = raw3915step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3915step3 raw3915step3Labels = mixedMoment B raw3915step4 raw3915step4Labels := by
      have ha : raw3915step4 = raw3915step3 := by apply Matrix.ext; unfold raw3915step4 raw3915step3; decide +kernel
      have hl : raw3915step3Labels = labelEmbedding6 ∘ raw3915step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3915step3 raw3915step3Labels raw3915step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw3916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3916step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3916step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw3916step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3916step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3916step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3916step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3916step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3916 raw3916Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw3916 raw3916Labels = mixedMoment B raw3916step0 raw3916step0Labels := by
      have hz : ∀ j, raw3916 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3916step0 = (fun i j => raw3916 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3916step0 raw3916; decide +kernel
      have hl : raw3916step0Labels = raw3916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3916 raw3916Labels permutation434 hz
    mixedMoment B raw3916step0 raw3916step0Labels = mixedMoment B raw3916step1 raw3916step1Labels := by
      have hz : ∀ j, raw3916step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3916step1 = (fun i j => raw3916step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3916step1 raw3916step0; decide +kernel
      have hl : raw3916step1Labels = raw3916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3916step0 raw3916step0Labels permutation80 hz
    mixedMoment B raw3916step1 raw3916step1Labels = mixedMoment B raw3916step2 raw3916step2Labels := by
      have ha : raw3916step2 = (fun i j => raw3916step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3916step2 raw3916step1; decide +kernel
      have hl : raw3916step2Labels = raw3916step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3916step1 raw3916step1Labels permutation9 permutation7
    mixedMoment B raw3916step2 raw3916step2Labels = mixedMoment B raw3916step3 raw3916step3Labels := by
      have ha : raw3916step3 = -raw3916step2 := by apply Matrix.ext; change ∀ i j, raw3916step3 i j = -(raw3916step2 i j); unfold raw3916step3 raw3916step2; decide +kernel
      have hl : raw3916step3Labels = raw3916step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3916step3 raw3916step3Labels = mixedMoment B raw3916step4 raw3916step4Labels := by
      have ha : raw3916step4 = raw3916step3 := by apply Matrix.ext; unfold raw3916step4 raw3916step3; decide +kernel
      have hl : raw3916step3Labels = labelEmbedding10 ∘ raw3916step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3916step3 raw3916step3Labels raw3916step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw3917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3917step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![3, -2, -1]]
def raw3917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw3917step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3917step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw3917step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3917 raw3917Labels = mixedMoment B node4573 node4573Labels := by
  calc
    mixedMoment B raw3917 raw3917Labels = mixedMoment B raw3917step0 raw3917step0Labels := by
      have hz : ∀ j, raw3917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3917step0 = (fun i j => raw3917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3917step0 raw3917; decide +kernel
      have hl : raw3917step0Labels = raw3917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3917 raw3917Labels permutation434 hz
    mixedMoment B raw3917step0 raw3917step0Labels = mixedMoment B raw3917step1 raw3917step1Labels := by
      have hz : ∀ j, raw3917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3917step1 = (fun i j => raw3917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3917step1 raw3917step0; decide +kernel
      have hl : raw3917step1Labels = raw3917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3917step0 raw3917step0Labels permutation80 hz
    mixedMoment B raw3917step1 raw3917step1Labels = mixedMoment B raw3917step2 raw3917step2Labels := by
      have ha : raw3917step2 = (fun i j => raw3917step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3917step2 raw3917step1; decide +kernel
      have hl : raw3917step2Labels = raw3917step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3917step1 raw3917step1Labels permutation10 permutation3
    mixedMoment B raw3917step2 raw3917step2Labels = mixedMoment B raw3917step3 raw3917step3Labels := by
      have ha : raw3917step3 = raw3917step2 := by apply Matrix.ext; unfold raw3917step3 raw3917step2; decide +kernel
      have hl : raw3917step2Labels = labelEmbedding6 ∘ raw3917step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3917step2 raw3917step2Labels raw3917step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4573 node4573Labels := by rfl

def raw3918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3918step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3918step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3918step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3918step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3918 raw3918Labels = mixedMoment B node5008 node5008Labels := by
  calc
    mixedMoment B raw3918 raw3918Labels = mixedMoment B raw3918step0 raw3918step0Labels := by
      have hz : ∀ j, raw3918 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3918step0 = (fun i j => raw3918 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3918step0 raw3918; decide +kernel
      have hl : raw3918step0Labels = raw3918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3918 raw3918Labels permutation434 hz
    mixedMoment B raw3918step0 raw3918step0Labels = mixedMoment B raw3918step1 raw3918step1Labels := by
      have ha : raw3918step1 = (fun i j => raw3918step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3918step1 raw3918step0; decide +kernel
      have hl : raw3918step1Labels = raw3918step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3918step0 raw3918step0Labels permutation139 permutation3
    mixedMoment B raw3918step1 raw3918step1Labels = mixedMoment B raw3918step2 raw3918step2Labels := by
      have ha : raw3918step2 = -raw3918step1 := by apply Matrix.ext; change ∀ i j, raw3918step2 i j = -(raw3918step1 i j); unfold raw3918step2 raw3918step1; decide +kernel
      have hl : raw3918step2Labels = raw3918step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3918step2 raw3918step2Labels = mixedMoment B raw3918step3 raw3918step3Labels := by
      have ha : raw3918step3 = raw3918step2 := by apply Matrix.ext; unfold raw3918step3 raw3918step2; decide +kernel
      have hl : raw3918step2Labels = labelEmbedding6 ∘ raw3918step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3918step2 raw3918step2Labels raw3918step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5008 node5008Labels := by rfl

def raw3919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3919step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3919step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3919step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3919step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3919 raw3919Labels = mixedMoment B node5008 node5008Labels := by
  calc
    mixedMoment B raw3919 raw3919Labels = mixedMoment B raw3919step0 raw3919step0Labels := by
      have hz : ∀ j, raw3919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3919step0 = (fun i j => raw3919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3919step0 raw3919; decide +kernel
      have hl : raw3919step0Labels = raw3919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3919 raw3919Labels permutation346 hz
    mixedMoment B raw3919step0 raw3919step0Labels = mixedMoment B raw3919step1 raw3919step1Labels := by
      have ha : raw3919step1 = (fun i j => raw3919step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3919step1 raw3919step0; decide +kernel
      have hl : raw3919step1Labels = raw3919step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3919step0 raw3919step0Labels permutation139 permutation3
    mixedMoment B raw3919step1 raw3919step1Labels = mixedMoment B raw3919step2 raw3919step2Labels := by
      have ha : raw3919step2 = -raw3919step1 := by apply Matrix.ext; change ∀ i j, raw3919step2 i j = -(raw3919step1 i j); unfold raw3919step2 raw3919step1; decide +kernel
      have hl : raw3919step2Labels = raw3919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3919step2 raw3919step2Labels = mixedMoment B raw3919step3 raw3919step3Labels := by
      have ha : raw3919step3 = raw3919step2 := by apply Matrix.ext; unfold raw3919step3 raw3919step2; decide +kernel
      have hl : raw3919step2Labels = labelEmbedding6 ∘ raw3919step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3919step2 raw3919step2Labels raw3919step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5008 node5008Labels := by rfl

def raw3920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw3920step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, -2, 3], ![-3, 2, 1]]
def raw3920step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3920step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw3920step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3920step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw3920step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3920 raw3920Labels = mixedMoment B node5022 node5022Labels := by
  calc
    mixedMoment B raw3920 raw3920Labels = mixedMoment B raw3920step0 raw3920step0Labels := by
      have hz : ∀ j, raw3920 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3920step0 = (fun i j => raw3920 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3920step0 raw3920; decide +kernel
      have hl : raw3920step0Labels = raw3920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3920 raw3920Labels permutation434 hz
    mixedMoment B raw3920step0 raw3920step0Labels = mixedMoment B raw3920step1 raw3920step1Labels := by
      have hz : ∀ j, raw3920step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3920step1 = (fun i j => raw3920step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3920step1 raw3920step0; decide +kernel
      have hl : raw3920step1Labels = raw3920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3920step0 raw3920step0Labels permutation80 hz
    mixedMoment B raw3920step1 raw3920step1Labels = mixedMoment B raw3920step2 raw3920step2Labels := by
      have ha : raw3920step2 = (fun i j => raw3920step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3920step2 raw3920step1; decide +kernel
      have hl : raw3920step2Labels = raw3920step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3920step1 raw3920step1Labels permutation29 permutation3
    mixedMoment B raw3920step2 raw3920step2Labels = mixedMoment B raw3920step3 raw3920step3Labels := by
      have ha : raw3920step3 = -raw3920step2 := by apply Matrix.ext; change ∀ i j, raw3920step3 i j = -(raw3920step2 i j); unfold raw3920step3 raw3920step2; decide +kernel
      have hl : raw3920step3Labels = raw3920step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3920step3 raw3920step3Labels = mixedMoment B raw3920step4 raw3920step4Labels := by
      have ha : raw3920step4 = raw3920step3 := by apply Matrix.ext; unfold raw3920step4 raw3920step3; decide +kernel
      have hl : raw3920step3Labels = labelEmbedding6 ∘ raw3920step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3920step3 raw3920step3Labels raw3920step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5022 node5022Labels := by rfl

def raw3921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw3921step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3921 raw3921Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw3921 raw3921Labels = mixedMoment B raw3921step0 raw3921step0Labels := by
      have hz : ∀ j, raw3921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3921step0 = (fun i j => raw3921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3921step0 raw3921; decide +kernel
      have hl : raw3921step0Labels = raw3921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3921 raw3921Labels permutation434 hz
    mixedMoment B raw3921step0 raw3921step0Labels = mixedMoment B raw3921step1 raw3921step1Labels := by
      have hz : ∀ j, raw3921step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3921step1 = (fun i j => raw3921step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3921step1 raw3921step0; decide +kernel
      have hl : raw3921step1Labels = raw3921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3921step0 raw3921step0Labels permutation80 hz
    mixedMoment B raw3921step1 raw3921step1Labels = mixedMoment B raw3921step2 raw3921step2Labels := by
      have ha : raw3921step2 = (fun i j => raw3921step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3921step2 raw3921step1; decide +kernel
      have hl : raw3921step2Labels = raw3921step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3921step1 raw3921step1Labels permutation10 permutation2
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw3922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw3922step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw3922step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3922 raw3922Labels = mixedMoment B node4564 node4564Labels := by
  calc
    mixedMoment B raw3922 raw3922Labels = mixedMoment B raw3922step0 raw3922step0Labels := by
      have hz : ∀ j, raw3922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3922step0 = (fun i j => raw3922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3922step0 raw3922; decide +kernel
      have hl : raw3922step0Labels = raw3922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3922 raw3922Labels permutation434 hz
    mixedMoment B raw3922step0 raw3922step0Labels = mixedMoment B raw3922step1 raw3922step1Labels := by
      have ha : raw3922step1 = (fun i j => raw3922step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3922step1 raw3922step0; decide +kernel
      have hl : raw3922step1Labels = raw3922step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3922step0 raw3922step0Labels permutation44 permutation3
    mixedMoment B raw3922step1 raw3922step1Labels = mixedMoment B raw3922step2 raw3922step2Labels := by
      have ha : raw3922step2 = raw3922step1 := by apply Matrix.ext; unfold raw3922step2 raw3922step1; decide +kernel
      have hl : raw3922step1Labels = labelEmbedding6 ∘ raw3922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3922step1 raw3922step1Labels raw3922step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4564 node4564Labels := by rfl

def raw3923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3923 raw3923Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw3923 raw3923Labels = mixedMoment B raw3923step0 raw3923step0Labels := by
      have hz : ∀ j, raw3923 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3923step0 = (fun i j => raw3923 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3923step0 raw3923; decide +kernel
      have hl : raw3923step0Labels = raw3923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3923 raw3923Labels permutation434 hz
    mixedMoment B raw3923step0 raw3923step0Labels = mixedMoment B raw3923step1 raw3923step1Labels := by
      have ha : raw3923step1 = (fun i j => raw3923step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3923step1 raw3923step0; decide +kernel
      have hl : raw3923step1Labels = raw3923step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3923step0 raw3923step0Labels permutation34 permutation2
    _ = mixedMoment B node5087 node5087Labels := by rfl

def raw3924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3924step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3924step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3924step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3924step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3924 raw3924Labels = mixedMoment B node5052 node5052Labels := by
  calc
    mixedMoment B raw3924 raw3924Labels = mixedMoment B raw3924step0 raw3924step0Labels := by
      have ha : raw3924step0 = (fun i j => raw3924 (permutation634 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3924step0 raw3924; decide +kernel
      have hl : raw3924step0Labels = raw3924Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3924 raw3924Labels permutation634 permutation3
    mixedMoment B raw3924step0 raw3924step0Labels = mixedMoment B raw3924step1 raw3924step1Labels := by
      have ha : raw3924step1 = -raw3924step0 := by apply Matrix.ext; change ∀ i j, raw3924step1 i j = -(raw3924step0 i j); unfold raw3924step1 raw3924step0; decide +kernel
      have hl : raw3924step1Labels = raw3924step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3924step1 raw3924step1Labels = mixedMoment B raw3924step2 raw3924step2Labels := by
      have ha : raw3924step2 = raw3924step1 := by apply Matrix.ext; unfold raw3924step2 raw3924step1; decide +kernel
      have hl : raw3924step1Labels = labelEmbedding6 ∘ raw3924step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3924step1 raw3924step1Labels raw3924step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5052 node5052Labels := by rfl

def raw3925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw3925step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw3925step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3925step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw3925step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3925 raw3925Labels = mixedMoment B node5062 node5062Labels := by
  calc
    mixedMoment B raw3925 raw3925Labels = mixedMoment B raw3925step0 raw3925step0Labels := by
      have hz : ∀ j, raw3925 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3925step0 = (fun i j => raw3925 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3925step0 raw3925; decide +kernel
      have hl : raw3925step0Labels = raw3925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3925 raw3925Labels permutation434 hz
    mixedMoment B raw3925step0 raw3925step0Labels = mixedMoment B raw3925step1 raw3925step1Labels := by
      have ha : raw3925step1 = (fun i j => raw3925step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3925step1 raw3925step0; decide +kernel
      have hl : raw3925step1Labels = raw3925step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3925step0 raw3925step0Labels permutation143 permutation3
    mixedMoment B raw3925step1 raw3925step1Labels = mixedMoment B raw3925step2 raw3925step2Labels := by
      have ha : raw3925step2 = -raw3925step1 := by apply Matrix.ext; change ∀ i j, raw3925step2 i j = -(raw3925step1 i j); unfold raw3925step2 raw3925step1; decide +kernel
      have hl : raw3925step2Labels = raw3925step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3925step2 raw3925step2Labels = mixedMoment B raw3925step3 raw3925step3Labels := by
      have ha : raw3925step3 = raw3925step2 := by apply Matrix.ext; unfold raw3925step3 raw3925step2; decide +kernel
      have hl : raw3925step2Labels = labelEmbedding6 ∘ raw3925step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3925step2 raw3925step2Labels raw3925step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5062 node5062Labels := by rfl

def raw3926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw3926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3926 raw3926Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw3926 raw3926Labels = mixedMoment B raw3926step0 raw3926step0Labels := by
      have hz : ∀ j, raw3926 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3926step0 = (fun i j => raw3926 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3926step0 raw3926; decide +kernel
      have hl : raw3926step0Labels = raw3926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3926 raw3926Labels permutation434 hz
    mixedMoment B raw3926step0 raw3926step0Labels = mixedMoment B raw3926step1 raw3926step1Labels := by
      have ha : raw3926step1 = (fun i j => raw3926step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3926step1 raw3926step0; decide +kernel
      have hl : raw3926step1Labels = raw3926step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3926step0 raw3926step0Labels permutation34 permutation2
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw3927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw3927step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw3927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3927 raw3927Labels = mixedMoment B node4564 node4564Labels := by
  calc
    mixedMoment B raw3927 raw3927Labels = mixedMoment B raw3927step0 raw3927step0Labels := by
      have hz : ∀ j, raw3927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3927step0 = (fun i j => raw3927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3927step0 raw3927; decide +kernel
      have hl : raw3927step0Labels = raw3927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3927 raw3927Labels permutation346 hz
    mixedMoment B raw3927step0 raw3927step0Labels = mixedMoment B raw3927step1 raw3927step1Labels := by
      have ha : raw3927step1 = (fun i j => raw3927step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3927step1 raw3927step0; decide +kernel
      have hl : raw3927step1Labels = raw3927step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3927step0 raw3927step0Labels permutation44 permutation3
    mixedMoment B raw3927step1 raw3927step1Labels = mixedMoment B raw3927step2 raw3927step2Labels := by
      have ha : raw3927step2 = raw3927step1 := by apply Matrix.ext; unfold raw3927step2 raw3927step1; decide +kernel
      have hl : raw3927step1Labels = labelEmbedding6 ∘ raw3927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3927step1 raw3927step1Labels raw3927step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4564 node4564Labels := by rfl

def raw3928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3928 raw3928Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw3928 raw3928Labels = mixedMoment B raw3928step0 raw3928step0Labels := by
      have hz : ∀ j, raw3928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3928step0 = (fun i j => raw3928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3928step0 raw3928; decide +kernel
      have hl : raw3928step0Labels = raw3928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3928 raw3928Labels permutation346 hz
    mixedMoment B raw3928step0 raw3928step0Labels = mixedMoment B raw3928step1 raw3928step1Labels := by
      have ha : raw3928step1 = (fun i j => raw3928step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3928step1 raw3928step0; decide +kernel
      have hl : raw3928step1Labels = raw3928step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3928step0 raw3928step0Labels permutation34 permutation2
    _ = mixedMoment B node5087 node5087Labels := by rfl

def raw3929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3929step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3929step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3929step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3929step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3929 raw3929Labels = mixedMoment B node5052 node5052Labels := by
  calc
    mixedMoment B raw3929 raw3929Labels = mixedMoment B raw3929step0 raw3929step0Labels := by
      have ha : raw3929step0 = (fun i j => raw3929 (permutation654 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3929step0 raw3929; decide +kernel
      have hl : raw3929step0Labels = raw3929Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3929 raw3929Labels permutation654 permutation3
    mixedMoment B raw3929step0 raw3929step0Labels = mixedMoment B raw3929step1 raw3929step1Labels := by
      have ha : raw3929step1 = -raw3929step0 := by apply Matrix.ext; change ∀ i j, raw3929step1 i j = -(raw3929step0 i j); unfold raw3929step1 raw3929step0; decide +kernel
      have hl : raw3929step1Labels = raw3929step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3929step1 raw3929step1Labels = mixedMoment B raw3929step2 raw3929step2Labels := by
      have ha : raw3929step2 = raw3929step1 := by apply Matrix.ext; unfold raw3929step2 raw3929step1; decide +kernel
      have hl : raw3929step1Labels = labelEmbedding6 ∘ raw3929step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3929step1 raw3929step1Labels raw3929step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5052 node5052Labels := by rfl

def raw3930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw3930step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw3930step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3930step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw3930step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3930 raw3930Labels = mixedMoment B node5062 node5062Labels := by
  calc
    mixedMoment B raw3930 raw3930Labels = mixedMoment B raw3930step0 raw3930step0Labels := by
      have hz : ∀ j, raw3930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3930step0 = (fun i j => raw3930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3930step0 raw3930; decide +kernel
      have hl : raw3930step0Labels = raw3930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3930 raw3930Labels permutation346 hz
    mixedMoment B raw3930step0 raw3930step0Labels = mixedMoment B raw3930step1 raw3930step1Labels := by
      have ha : raw3930step1 = (fun i j => raw3930step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3930step1 raw3930step0; decide +kernel
      have hl : raw3930step1Labels = raw3930step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3930step0 raw3930step0Labels permutation143 permutation3
    mixedMoment B raw3930step1 raw3930step1Labels = mixedMoment B raw3930step2 raw3930step2Labels := by
      have ha : raw3930step2 = -raw3930step1 := by apply Matrix.ext; change ∀ i j, raw3930step2 i j = -(raw3930step1 i j); unfold raw3930step2 raw3930step1; decide +kernel
      have hl : raw3930step2Labels = raw3930step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3930step2 raw3930step2Labels = mixedMoment B raw3930step3 raw3930step3Labels := by
      have ha : raw3930step3 = raw3930step2 := by apply Matrix.ext; unfold raw3930step3 raw3930step2; decide +kernel
      have hl : raw3930step2Labels = labelEmbedding6 ∘ raw3930step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3930step2 raw3930step2Labels raw3930step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5062 node5062Labels := by rfl

def raw3931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw3931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3931 raw3931Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw3931 raw3931Labels = mixedMoment B raw3931step0 raw3931step0Labels := by
      have hz : ∀ j, raw3931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3931step0 = (fun i j => raw3931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3931step0 raw3931; decide +kernel
      have hl : raw3931step0Labels = raw3931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3931 raw3931Labels permutation346 hz
    mixedMoment B raw3931step0 raw3931step0Labels = mixedMoment B raw3931step1 raw3931step1Labels := by
      have ha : raw3931step1 = (fun i j => raw3931step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3931step1 raw3931step0; decide +kernel
      have hl : raw3931step1Labels = raw3931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3931step0 raw3931step0Labels permutation34 permutation2
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw3932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3932 raw3932Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw3932 raw3932Labels = mixedMoment B raw3932step0 raw3932step0Labels := by
      have hz : ∀ j, raw3932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3932step0 = (fun i j => raw3932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3932step0 raw3932; decide +kernel
      have hl : raw3932step0Labels = raw3932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3932 raw3932Labels permutation434 hz
    mixedMoment B raw3932step0 raw3932step0Labels = mixedMoment B raw3932step1 raw3932step1Labels := by
      have hz : ∀ j, raw3932step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3932step1 = (fun i j => raw3932step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3932step1 raw3932step0; decide +kernel
      have hl : raw3932step1Labels = raw3932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3932step0 raw3932step0Labels permutation80 hz
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw3933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3933 raw3933Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw3933 raw3933Labels = mixedMoment B raw3933step0 raw3933step0Labels := by
      have hz : ∀ j, raw3933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3933step0 = (fun i j => raw3933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3933step0 raw3933; decide +kernel
      have hl : raw3933step0Labels = raw3933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3933 raw3933Labels permutation434 hz
    mixedMoment B raw3933step0 raw3933step0Labels = mixedMoment B raw3933step1 raw3933step1Labels := by
      have hz : ∀ j, raw3933step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3933step1 = (fun i j => raw3933step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3933step1 raw3933step0; decide +kernel
      have hl : raw3933step1Labels = raw3933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3933step0 raw3933step0Labels permutation80 hz
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw3934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3934 raw3934Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw3934 raw3934Labels = mixedMoment B raw3934step0 raw3934step0Labels := by
      have hz : ∀ j, raw3934 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3934step0 = (fun i j => raw3934 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3934step0 raw3934; decide +kernel
      have hl : raw3934step0Labels = raw3934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3934 raw3934Labels permutation434 hz
    mixedMoment B raw3934step0 raw3934step0Labels = mixedMoment B raw3934step1 raw3934step1Labels := by
      have ha : raw3934step1 = (fun i j => raw3934step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3934step1 raw3934step0; decide +kernel
      have hl : raw3934step1Labels = raw3934step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3934step0 raw3934step0Labels permutation38 permutation2
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw3935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3935 raw3935Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw3935 raw3935Labels = mixedMoment B raw3935step0 raw3935step0Labels := by
      have hz : ∀ j, raw3935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3935step0 = (fun i j => raw3935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3935step0 raw3935; decide +kernel
      have hl : raw3935step0Labels = raw3935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3935 raw3935Labels permutation346 hz
    mixedMoment B raw3935step0 raw3935step0Labels = mixedMoment B raw3935step1 raw3935step1Labels := by
      have ha : raw3935step1 = (fun i j => raw3935step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3935step1 raw3935step0; decide +kernel
      have hl : raw3935step1Labels = raw3935step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3935step0 raw3935step0Labels permutation38 permutation2
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw3936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3936 raw3936Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw3936 raw3936Labels = mixedMoment B raw3936step0 raw3936step0Labels := by
      have hz : ∀ j, raw3936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3936step0 = (fun i j => raw3936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3936step0 raw3936; decide +kernel
      have hl : raw3936step0Labels = raw3936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3936 raw3936Labels permutation434 hz
    mixedMoment B raw3936step0 raw3936step0Labels = mixedMoment B raw3936step1 raw3936step1Labels := by
      have hz : ∀ j, raw3936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3936step1 = (fun i j => raw3936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3936step1 raw3936step0; decide +kernel
      have hl : raw3936step1Labels = raw3936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3936step0 raw3936step0Labels permutation80 hz
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw3937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw3937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3937step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-4, 2, 2]]
def raw3937step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3937step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw3937step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3937step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw3937step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3937 raw3937Labels = mixedMoment B node4413 node4413Labels := by
  calc
    mixedMoment B raw3937 raw3937Labels = mixedMoment B raw3937step0 raw3937step0Labels := by
      have hz : ∀ j, raw3937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3937step0 = (fun i j => raw3937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3937step0 raw3937; decide +kernel
      have hl : raw3937step0Labels = raw3937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3937 raw3937Labels permutation434 hz
    mixedMoment B raw3937step0 raw3937step0Labels = mixedMoment B raw3937step1 raw3937step1Labels := by
      have hz : ∀ j, raw3937step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3937step1 = (fun i j => raw3937step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3937step1 raw3937step0; decide +kernel
      have hl : raw3937step1Labels = raw3937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3937step0 raw3937step0Labels permutation80 hz
    mixedMoment B raw3937step1 raw3937step1Labels = mixedMoment B raw3937step2 raw3937step2Labels := by
      have ha : raw3937step2 = (fun i j => raw3937step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3937step2 raw3937step1; decide +kernel
      have hl : raw3937step2Labels = raw3937step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3937step1 raw3937step1Labels permutation29 permutation3
    mixedMoment B raw3937step2 raw3937step2Labels = mixedMoment B raw3937step3 raw3937step3Labels := by
      have ha : raw3937step3 = -raw3937step2 := by apply Matrix.ext; change ∀ i j, raw3937step3 i j = -(raw3937step2 i j); unfold raw3937step3 raw3937step2; decide +kernel
      have hl : raw3937step3Labels = raw3937step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3937step3 raw3937step3Labels = mixedMoment B raw3937step4 raw3937step4Labels := by
      have ha : raw3937step4 = raw3937step3 := by apply Matrix.ext; unfold raw3937step4 raw3937step3; decide +kernel
      have hl : raw3937step3Labels = labelEmbedding6 ∘ raw3937step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3937step3 raw3937step3Labels raw3937step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4413 node4413Labels := by rfl

def raw3938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![4, -3, -1]]
def raw3938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw3938step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3938step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3938step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3938step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3938step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3938 raw3938Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw3938 raw3938Labels = mixedMoment B raw3938step0 raw3938step0Labels := by
      have hz : ∀ j, raw3938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3938step0 = (fun i j => raw3938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3938step0 raw3938; decide +kernel
      have hl : raw3938step0Labels = raw3938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3938 raw3938Labels permutation434 hz
    mixedMoment B raw3938step0 raw3938step0Labels = mixedMoment B raw3938step1 raw3938step1Labels := by
      have hz : ∀ j, raw3938step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3938step1 = (fun i j => raw3938step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3938step1 raw3938step0; decide +kernel
      have hl : raw3938step1Labels = raw3938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3938step0 raw3938step0Labels permutation80 hz
    mixedMoment B raw3938step1 raw3938step1Labels = mixedMoment B raw3938step2 raw3938step2Labels := by
      have ha : raw3938step2 = (fun i j => raw3938step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3938step2 raw3938step1; decide +kernel
      have hl : raw3938step2Labels = raw3938step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3938step1 raw3938step1Labels permutation31 permutation3
    mixedMoment B raw3938step2 raw3938step2Labels = mixedMoment B raw3938step3 raw3938step3Labels := by
      have ha : raw3938step3 = -raw3938step2 := by apply Matrix.ext; change ∀ i j, raw3938step3 i j = -(raw3938step2 i j); unfold raw3938step3 raw3938step2; decide +kernel
      have hl : raw3938step3Labels = raw3938step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3938step3 raw3938step3Labels = mixedMoment B raw3938step4 raw3938step4Labels := by
      have ha : raw3938step4 = raw3938step3 := by apply Matrix.ext; unfold raw3938step4 raw3938step3; decide +kernel
      have hl : raw3938step3Labels = labelEmbedding6 ∘ raw3938step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3938step3 raw3938step3Labels raw3938step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw3939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3939step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3939step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3939step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3939 raw3939Labels = mixedMoment B node4410 node4410Labels := by
  calc
    mixedMoment B raw3939 raw3939Labels = mixedMoment B raw3939step0 raw3939step0Labels := by
      have hz : ∀ j, raw3939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3939step0 = (fun i j => raw3939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3939step0 raw3939; decide +kernel
      have hl : raw3939step0Labels = raw3939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3939 raw3939Labels permutation434 hz
    mixedMoment B raw3939step0 raw3939step0Labels = mixedMoment B raw3939step1 raw3939step1Labels := by
      have ha : raw3939step1 = (fun i j => raw3939step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3939step1 raw3939step0; decide +kernel
      have hl : raw3939step1Labels = raw3939step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3939step0 raw3939step0Labels permutation139 permutation3
    mixedMoment B raw3939step1 raw3939step1Labels = mixedMoment B raw3939step2 raw3939step2Labels := by
      have ha : raw3939step2 = -raw3939step1 := by apply Matrix.ext; change ∀ i j, raw3939step2 i j = -(raw3939step1 i j); unfold raw3939step2 raw3939step1; decide +kernel
      have hl : raw3939step2Labels = raw3939step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3939step2 raw3939step2Labels = mixedMoment B raw3939step3 raw3939step3Labels := by
      have ha : raw3939step3 = raw3939step2 := by apply Matrix.ext; unfold raw3939step3 raw3939step2; decide +kernel
      have hl : raw3939step2Labels = labelEmbedding6 ∘ raw3939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3939step2 raw3939step2Labels raw3939step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4410 node4410Labels := by rfl

def raw3940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3940step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3940step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3940step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3940step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3940 raw3940Labels = mixedMoment B node4410 node4410Labels := by
  calc
    mixedMoment B raw3940 raw3940Labels = mixedMoment B raw3940step0 raw3940step0Labels := by
      have hz : ∀ j, raw3940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3940step0 = (fun i j => raw3940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3940step0 raw3940; decide +kernel
      have hl : raw3940step0Labels = raw3940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3940 raw3940Labels permutation346 hz
    mixedMoment B raw3940step0 raw3940step0Labels = mixedMoment B raw3940step1 raw3940step1Labels := by
      have ha : raw3940step1 = (fun i j => raw3940step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3940step1 raw3940step0; decide +kernel
      have hl : raw3940step1Labels = raw3940step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3940step0 raw3940step0Labels permutation139 permutation3
    mixedMoment B raw3940step1 raw3940step1Labels = mixedMoment B raw3940step2 raw3940step2Labels := by
      have ha : raw3940step2 = -raw3940step1 := by apply Matrix.ext; change ∀ i j, raw3940step2 i j = -(raw3940step1 i j); unfold raw3940step2 raw3940step1; decide +kernel
      have hl : raw3940step2Labels = raw3940step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3940step2 raw3940step2Labels = mixedMoment B raw3940step3 raw3940step3Labels := by
      have ha : raw3940step3 = raw3940step2 := by apply Matrix.ext; unfold raw3940step3 raw3940step2; decide +kernel
      have hl : raw3940step2Labels = labelEmbedding6 ∘ raw3940step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3940step2 raw3940step2Labels raw3940step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4410 node4410Labels := by rfl

def raw3941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw3941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw3941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![4, -3, -1]]
def raw3941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw3941step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3941step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw3941step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3941step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw3941step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3941 raw3941Labels = mixedMoment B node4429 node4429Labels := by
  calc
    mixedMoment B raw3941 raw3941Labels = mixedMoment B raw3941step0 raw3941step0Labels := by
      have hz : ∀ j, raw3941 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3941step0 = (fun i j => raw3941 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3941step0 raw3941; decide +kernel
      have hl : raw3941step0Labels = raw3941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3941 raw3941Labels permutation434 hz
    mixedMoment B raw3941step0 raw3941step0Labels = mixedMoment B raw3941step1 raw3941step1Labels := by
      have hz : ∀ j, raw3941step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3941step1 = (fun i j => raw3941step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3941step1 raw3941step0; decide +kernel
      have hl : raw3941step1Labels = raw3941step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3941step0 raw3941step0Labels permutation80 hz
    mixedMoment B raw3941step1 raw3941step1Labels = mixedMoment B raw3941step2 raw3941step2Labels := by
      have ha : raw3941step2 = (fun i j => raw3941step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3941step2 raw3941step1; decide +kernel
      have hl : raw3941step2Labels = raw3941step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3941step1 raw3941step1Labels permutation29 permutation3
    mixedMoment B raw3941step2 raw3941step2Labels = mixedMoment B raw3941step3 raw3941step3Labels := by
      have ha : raw3941step3 = -raw3941step2 := by apply Matrix.ext; change ∀ i j, raw3941step3 i j = -(raw3941step2 i j); unfold raw3941step3 raw3941step2; decide +kernel
      have hl : raw3941step3Labels = raw3941step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3941step3 raw3941step3Labels = mixedMoment B raw3941step4 raw3941step4Labels := by
      have ha : raw3941step4 = raw3941step3 := by apply Matrix.ext; unfold raw3941step4 raw3941step3; decide +kernel
      have hl : raw3941step3Labels = labelEmbedding6 ∘ raw3941step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3941step3 raw3941step3Labels raw3941step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4429 node4429Labels := by rfl

def raw3942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3942Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3942step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![3, -2, -1]]
def raw3942step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw3942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3942step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3942 raw3942Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw3942 raw3942Labels = mixedMoment B raw3942step0 raw3942step0Labels := by
      have hz : ∀ j, raw3942 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3942step0 = (fun i j => raw3942 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3942step0 raw3942; decide +kernel
      have hl : raw3942step0Labels = raw3942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3942 raw3942Labels permutation434 hz
    mixedMoment B raw3942step0 raw3942step0Labels = mixedMoment B raw3942step1 raw3942step1Labels := by
      have hz : ∀ j, raw3942step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3942step1 = (fun i j => raw3942step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3942step1 raw3942step0; decide +kernel
      have hl : raw3942step1Labels = raw3942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3942step0 raw3942step0Labels permutation80 hz
    mixedMoment B raw3942step1 raw3942step1Labels = mixedMoment B raw3942step2 raw3942step2Labels := by
      have ha : raw3942step2 = (fun i j => raw3942step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3942step2 raw3942step1; decide +kernel
      have hl : raw3942step2Labels = raw3942step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3942step1 raw3942step1Labels permutation31 permutation3
    mixedMoment B raw3942step2 raw3942step2Labels = mixedMoment B raw3942step3 raw3942step3Labels := by
      have ha : raw3942step3 = -raw3942step2 := by apply Matrix.ext; change ∀ i j, raw3942step3 i j = -(raw3942step2 i j); unfold raw3942step3 raw3942step2; decide +kernel
      have hl : raw3942step3Labels = raw3942step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw3943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw3943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3943 raw3943Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw3943 raw3943Labels = mixedMoment B raw3943step0 raw3943step0Labels := by
      have hz : ∀ j, raw3943 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3943step0 = (fun i j => raw3943 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3943step0 raw3943; decide +kernel
      have hl : raw3943step0Labels = raw3943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3943 raw3943Labels permutation434 hz
    mixedMoment B raw3943step0 raw3943step0Labels = mixedMoment B raw3943step1 raw3943step1Labels := by
      have ha : raw3943step1 = (fun i j => raw3943step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3943step1 raw3943step0; decide +kernel
      have hl : raw3943step1Labels = raw3943step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3943step0 raw3943step0Labels permutation139 permutation3
    mixedMoment B raw3943step1 raw3943step1Labels = mixedMoment B raw3943step2 raw3943step2Labels := by
      have ha : raw3943step2 = -raw3943step1 := by apply Matrix.ext; change ∀ i j, raw3943step2 i j = -(raw3943step1 i j); unfold raw3943step2 raw3943step1; decide +kernel
      have hl : raw3943step2Labels = raw3943step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw3944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw3944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3944 raw3944Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw3944 raw3944Labels = mixedMoment B raw3944step0 raw3944step0Labels := by
      have hz : ∀ j, raw3944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3944step0 = (fun i j => raw3944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3944step0 raw3944; decide +kernel
      have hl : raw3944step0Labels = raw3944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3944 raw3944Labels permutation346 hz
    mixedMoment B raw3944step0 raw3944step0Labels = mixedMoment B raw3944step1 raw3944step1Labels := by
      have ha : raw3944step1 = (fun i j => raw3944step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3944step1 raw3944step0; decide +kernel
      have hl : raw3944step1Labels = raw3944step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3944step0 raw3944step0Labels permutation139 permutation3
    mixedMoment B raw3944step1 raw3944step1Labels = mixedMoment B raw3944step2 raw3944step2Labels := by
      have ha : raw3944step2 = -raw3944step1 := by apply Matrix.ext; change ∀ i j, raw3944step2 i j = -(raw3944step1 i j); unfold raw3944step2 raw3944step1; decide +kernel
      have hl : raw3944step2Labels = raw3944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw3945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw3945step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw3945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3945step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw3945step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3945 raw3945Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw3945 raw3945Labels = mixedMoment B raw3945step0 raw3945step0Labels := by
      have hz : ∀ j, raw3945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3945step0 = (fun i j => raw3945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3945step0 raw3945; decide +kernel
      have hl : raw3945step0Labels = raw3945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3945 raw3945Labels permutation434 hz
    mixedMoment B raw3945step0 raw3945step0Labels = mixedMoment B raw3945step1 raw3945step1Labels := by
      have hz : ∀ j, raw3945step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3945step1 = (fun i j => raw3945step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3945step1 raw3945step0; decide +kernel
      have hl : raw3945step1Labels = raw3945step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3945step0 raw3945step0Labels permutation80 hz
    mixedMoment B raw3945step1 raw3945step1Labels = mixedMoment B raw3945step2 raw3945step2Labels := by
      have ha : raw3945step2 = (fun i j => raw3945step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3945step2 raw3945step1; decide +kernel
      have hl : raw3945step2Labels = raw3945step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3945step1 raw3945step1Labels permutation29 permutation3
    mixedMoment B raw3945step2 raw3945step2Labels = mixedMoment B raw3945step3 raw3945step3Labels := by
      have ha : raw3945step3 = -raw3945step2 := by apply Matrix.ext; change ∀ i j, raw3945step3 i j = -(raw3945step2 i j); unfold raw3945step3 raw3945step2; decide +kernel
      have hl : raw3945step3Labels = raw3945step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw3946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3946step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3946 raw3946Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw3946 raw3946Labels = mixedMoment B raw3946step0 raw3946step0Labels := by
      have hz : ∀ j, raw3946 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3946step0 = (fun i j => raw3946 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3946step0 raw3946; decide +kernel
      have hl : raw3946step0Labels = raw3946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3946 raw3946Labels permutation434 hz
    mixedMoment B raw3946step0 raw3946step0Labels = mixedMoment B raw3946step1 raw3946step1Labels := by
      have hz : ∀ j, raw3946step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3946step1 = (fun i j => raw3946step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3946step1 raw3946step0; decide +kernel
      have hl : raw3946step1Labels = raw3946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3946step0 raw3946step0Labels permutation80 hz
    mixedMoment B raw3946step1 raw3946step1Labels = mixedMoment B raw3946step2 raw3946step2Labels := by
      have ha : raw3946step2 = (fun i j => raw3946step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3946step2 raw3946step1; decide +kernel
      have hl : raw3946step2Labels = raw3946step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3946step1 raw3946step1Labels permutation25 permutation6
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw3947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![3, -2, -1]]
def raw3947step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw3947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3947 raw3947Labels = mixedMoment B node1191 node1191Labels := by
  calc
    mixedMoment B raw3947 raw3947Labels = mixedMoment B raw3947step0 raw3947step0Labels := by
      have hz : ∀ j, raw3947 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3947step0 = (fun i j => raw3947 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3947step0 raw3947; decide +kernel
      have hl : raw3947step0Labels = raw3947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3947 raw3947Labels permutation434 hz
    mixedMoment B raw3947step0 raw3947step0Labels = mixedMoment B raw3947step1 raw3947step1Labels := by
      have hz : ∀ j, raw3947step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3947step1 = (fun i j => raw3947step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3947step1 raw3947step0; decide +kernel
      have hl : raw3947step1Labels = raw3947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3947step0 raw3947step0Labels permutation80 hz
    mixedMoment B raw3947step1 raw3947step1Labels = mixedMoment B raw3947step2 raw3947step2Labels := by
      have ha : raw3947step2 = (fun i j => raw3947step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3947step2 raw3947step1; decide +kernel
      have hl : raw3947step2Labels = raw3947step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3947step1 raw3947step1Labels permutation10 permutation3
    _ = mixedMoment B node1191 node1191Labels := by rfl

def raw3948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3948 raw3948Labels = mixedMoment B node2393 node2393Labels := by
  calc
    mixedMoment B raw3948 raw3948Labels = mixedMoment B raw3948step0 raw3948step0Labels := by
      have hz : ∀ j, raw3948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3948step0 = (fun i j => raw3948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3948step0 raw3948; decide +kernel
      have hl : raw3948step0Labels = raw3948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3948 raw3948Labels permutation434 hz
    mixedMoment B raw3948step0 raw3948step0Labels = mixedMoment B raw3948step1 raw3948step1Labels := by
      have ha : raw3948step1 = (fun i j => raw3948step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3948step1 raw3948step0; decide +kernel
      have hl : raw3948step1Labels = raw3948step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3948step0 raw3948step0Labels permutation139 permutation3
    mixedMoment B raw3948step1 raw3948step1Labels = mixedMoment B raw3948step2 raw3948step2Labels := by
      have ha : raw3948step2 = -raw3948step1 := by apply Matrix.ext; change ∀ i j, raw3948step2 i j = -(raw3948step1 i j); unfold raw3948step2 raw3948step1; decide +kernel
      have hl : raw3948step2Labels = raw3948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2393 node2393Labels := by rfl

def raw3949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3949 raw3949Labels = mixedMoment B node2393 node2393Labels := by
  calc
    mixedMoment B raw3949 raw3949Labels = mixedMoment B raw3949step0 raw3949step0Labels := by
      have hz : ∀ j, raw3949 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3949step0 = (fun i j => raw3949 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3949step0 raw3949; decide +kernel
      have hl : raw3949step0Labels = raw3949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3949 raw3949Labels permutation346 hz
    mixedMoment B raw3949step0 raw3949step0Labels = mixedMoment B raw3949step1 raw3949step1Labels := by
      have ha : raw3949step1 = (fun i j => raw3949step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3949step1 raw3949step0; decide +kernel
      have hl : raw3949step1Labels = raw3949step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3949step0 raw3949step0Labels permutation139 permutation3
    mixedMoment B raw3949step1 raw3949step1Labels = mixedMoment B raw3949step2 raw3949step2Labels := by
      have ha : raw3949step2 = -raw3949step1 := by apply Matrix.ext; change ∀ i j, raw3949step2 i j = -(raw3949step1 i j); unfold raw3949step2 raw3949step1; decide +kernel
      have hl : raw3949step2Labels = raw3949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2393 node2393Labels := by rfl

def raw3950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw3950step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, -2, 3], ![-3, 2, 1]]
def raw3950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3950step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw3950step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3950 raw3950Labels = mixedMoment B node2408 node2408Labels := by
  calc
    mixedMoment B raw3950 raw3950Labels = mixedMoment B raw3950step0 raw3950step0Labels := by
      have hz : ∀ j, raw3950 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3950step0 = (fun i j => raw3950 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3950step0 raw3950; decide +kernel
      have hl : raw3950step0Labels = raw3950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3950 raw3950Labels permutation434 hz
    mixedMoment B raw3950step0 raw3950step0Labels = mixedMoment B raw3950step1 raw3950step1Labels := by
      have hz : ∀ j, raw3950step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3950step1 = (fun i j => raw3950step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3950step1 raw3950step0; decide +kernel
      have hl : raw3950step1Labels = raw3950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3950step0 raw3950step0Labels permutation80 hz
    mixedMoment B raw3950step1 raw3950step1Labels = mixedMoment B raw3950step2 raw3950step2Labels := by
      have ha : raw3950step2 = (fun i j => raw3950step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3950step2 raw3950step1; decide +kernel
      have hl : raw3950step2Labels = raw3950step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3950step1 raw3950step1Labels permutation29 permutation3
    mixedMoment B raw3950step2 raw3950step2Labels = mixedMoment B raw3950step3 raw3950step3Labels := by
      have ha : raw3950step3 = -raw3950step2 := by apply Matrix.ext; change ∀ i j, raw3950step3 i j = -(raw3950step2 i j); unfold raw3950step3 raw3950step2; decide +kernel
      have hl : raw3950step3Labels = raw3950step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2408 node2408Labels := by rfl

def raw3951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3951step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw3951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3951 raw3951Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw3951 raw3951Labels = mixedMoment B raw3951step0 raw3951step0Labels := by
      have hz : ∀ j, raw3951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3951step0 = (fun i j => raw3951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3951step0 raw3951; decide +kernel
      have hl : raw3951step0Labels = raw3951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3951 raw3951Labels permutation434 hz
    mixedMoment B raw3951step0 raw3951step0Labels = mixedMoment B raw3951step1 raw3951step1Labels := by
      have hz : ∀ j, raw3951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3951step1 = (fun i j => raw3951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3951step1 raw3951step0; decide +kernel
      have hl : raw3951step1Labels = raw3951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3951step0 raw3951step0Labels permutation80 hz
    mixedMoment B raw3951step1 raw3951step1Labels = mixedMoment B raw3951step2 raw3951step2Labels := by
      have ha : raw3951step2 = (fun i j => raw3951step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3951step2 raw3951step1; decide +kernel
      have hl : raw3951step2Labels = raw3951step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3951step1 raw3951step1Labels permutation10 permutation3
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw3952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw3952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3952 raw3952Labels = mixedMoment B node1181 node1181Labels := by
  calc
    mixedMoment B raw3952 raw3952Labels = mixedMoment B raw3952step0 raw3952step0Labels := by
      have hz : ∀ j, raw3952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3952step0 = (fun i j => raw3952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3952step0 raw3952; decide +kernel
      have hl : raw3952step0Labels = raw3952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3952 raw3952Labels permutation434 hz
    mixedMoment B raw3952step0 raw3952step0Labels = mixedMoment B raw3952step1 raw3952step1Labels := by
      have ha : raw3952step1 = (fun i j => raw3952step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3952step1 raw3952step0; decide +kernel
      have hl : raw3952step1Labels = raw3952step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3952step0 raw3952step0Labels permutation44 permutation3
    _ = mixedMoment B node1181 node1181Labels := by rfl

def raw3953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw3953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3953 raw3953Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw3953 raw3953Labels = mixedMoment B raw3953step0 raw3953step0Labels := by
      have hz : ∀ j, raw3953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3953step0 = (fun i j => raw3953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3953step0 raw3953; decide +kernel
      have hl : raw3953step0Labels = raw3953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3953 raw3953Labels permutation434 hz
    mixedMoment B raw3953step0 raw3953step0Labels = mixedMoment B raw3953step1 raw3953step1Labels := by
      have ha : raw3953step1 = (fun i j => raw3953step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3953step1 raw3953step0; decide +kernel
      have hl : raw3953step1Labels = raw3953step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3953step0 raw3953step0Labels permutation145 permutation3
    mixedMoment B raw3953step1 raw3953step1Labels = mixedMoment B raw3953step2 raw3953step2Labels := by
      have ha : raw3953step2 = -raw3953step1 := by apply Matrix.ext; change ∀ i j, raw3953step2 i j = -(raw3953step1 i j); unfold raw3953step2 raw3953step1; decide +kernel
      have hl : raw3953step2Labels = raw3953step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2495 node2495Labels := by rfl

def raw3954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3954 raw3954Labels = mixedMoment B node2454 node2454Labels := by
  calc
    mixedMoment B raw3954 raw3954Labels = mixedMoment B raw3954step0 raw3954step0Labels := by
      have ha : raw3954step0 = (fun i j => raw3954 (permutation634 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3954step0 raw3954; decide +kernel
      have hl : raw3954step0Labels = raw3954Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3954 raw3954Labels permutation634 permutation3
    mixedMoment B raw3954step0 raw3954step0Labels = mixedMoment B raw3954step1 raw3954step1Labels := by
      have ha : raw3954step1 = -raw3954step0 := by apply Matrix.ext; change ∀ i j, raw3954step1 i j = -(raw3954step0 i j); unfold raw3954step1 raw3954step0; decide +kernel
      have hl : raw3954step1Labels = raw3954step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2454 node2454Labels := by rfl

def raw3955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3955step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw3955step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw3955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3955 raw3955Labels = mixedMoment B node2465 node2465Labels := by
  calc
    mixedMoment B raw3955 raw3955Labels = mixedMoment B raw3955step0 raw3955step0Labels := by
      have hz : ∀ j, raw3955 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3955step0 = (fun i j => raw3955 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3955step0 raw3955; decide +kernel
      have hl : raw3955step0Labels = raw3955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3955 raw3955Labels permutation434 hz
    mixedMoment B raw3955step0 raw3955step0Labels = mixedMoment B raw3955step1 raw3955step1Labels := by
      have ha : raw3955step1 = (fun i j => raw3955step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3955step1 raw3955step0; decide +kernel
      have hl : raw3955step1Labels = raw3955step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3955step0 raw3955step0Labels permutation143 permutation3
    mixedMoment B raw3955step1 raw3955step1Labels = mixedMoment B raw3955step2 raw3955step2Labels := by
      have ha : raw3955step2 = -raw3955step1 := by apply Matrix.ext; change ∀ i j, raw3955step2 i j = -(raw3955step1 i j); unfold raw3955step2 raw3955step1; decide +kernel
      have hl : raw3955step2Labels = raw3955step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2465 node2465Labels := by rfl

def raw3956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3956step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3956 raw3956Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw3956 raw3956Labels = mixedMoment B raw3956step0 raw3956step0Labels := by
      have hz : ∀ j, raw3956 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3956step0 = (fun i j => raw3956 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3956step0 raw3956; decide +kernel
      have hl : raw3956step0Labels = raw3956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3956 raw3956Labels permutation434 hz
    mixedMoment B raw3956step0 raw3956step0Labels = mixedMoment B raw3956step1 raw3956step1Labels := by
      have ha : raw3956step1 = (fun i j => raw3956step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3956step1 raw3956step0; decide +kernel
      have hl : raw3956step1Labels = raw3956step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3956step0 raw3956step0Labels permutation44 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw3957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw3957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3957 raw3957Labels = mixedMoment B node1181 node1181Labels := by
  calc
    mixedMoment B raw3957 raw3957Labels = mixedMoment B raw3957step0 raw3957step0Labels := by
      have hz : ∀ j, raw3957 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3957step0 = (fun i j => raw3957 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3957step0 raw3957; decide +kernel
      have hl : raw3957step0Labels = raw3957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3957 raw3957Labels permutation346 hz
    mixedMoment B raw3957step0 raw3957step0Labels = mixedMoment B raw3957step1 raw3957step1Labels := by
      have ha : raw3957step1 = (fun i j => raw3957step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3957step1 raw3957step0; decide +kernel
      have hl : raw3957step1Labels = raw3957step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3957step0 raw3957step0Labels permutation44 permutation3
    _ = mixedMoment B node1181 node1181Labels := by rfl

def raw3958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw3958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3958 raw3958Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw3958 raw3958Labels = mixedMoment B raw3958step0 raw3958step0Labels := by
      have hz : ∀ j, raw3958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3958step0 = (fun i j => raw3958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3958step0 raw3958; decide +kernel
      have hl : raw3958step0Labels = raw3958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3958 raw3958Labels permutation346 hz
    mixedMoment B raw3958step0 raw3958step0Labels = mixedMoment B raw3958step1 raw3958step1Labels := by
      have ha : raw3958step1 = (fun i j => raw3958step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3958step1 raw3958step0; decide +kernel
      have hl : raw3958step1Labels = raw3958step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3958step0 raw3958step0Labels permutation145 permutation3
    mixedMoment B raw3958step1 raw3958step1Labels = mixedMoment B raw3958step2 raw3958step2Labels := by
      have ha : raw3958step2 = -raw3958step1 := by apply Matrix.ext; change ∀ i j, raw3958step2 i j = -(raw3958step1 i j); unfold raw3958step2 raw3958step1; decide +kernel
      have hl : raw3958step2Labels = raw3958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2495 node2495Labels := by rfl

def raw3959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3959 raw3959Labels = mixedMoment B node2454 node2454Labels := by
  calc
    mixedMoment B raw3959 raw3959Labels = mixedMoment B raw3959step0 raw3959step0Labels := by
      have ha : raw3959step0 = (fun i j => raw3959 (permutation654 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3959step0 raw3959; decide +kernel
      have hl : raw3959step0Labels = raw3959Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3959 raw3959Labels permutation654 permutation3
    mixedMoment B raw3959step0 raw3959step0Labels = mixedMoment B raw3959step1 raw3959step1Labels := by
      have ha : raw3959step1 = -raw3959step0 := by apply Matrix.ext; change ∀ i j, raw3959step1 i j = -(raw3959step0 i j); unfold raw3959step1 raw3959step0; decide +kernel
      have hl : raw3959step1Labels = raw3959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2454 node2454Labels := by rfl

def raw3960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw3960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw3960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3960 raw3960Labels = mixedMoment B node2465 node2465Labels := by
  calc
    mixedMoment B raw3960 raw3960Labels = mixedMoment B raw3960step0 raw3960step0Labels := by
      have hz : ∀ j, raw3960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3960step0 = (fun i j => raw3960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3960step0 raw3960; decide +kernel
      have hl : raw3960step0Labels = raw3960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3960 raw3960Labels permutation346 hz
    mixedMoment B raw3960step0 raw3960step0Labels = mixedMoment B raw3960step1 raw3960step1Labels := by
      have ha : raw3960step1 = (fun i j => raw3960step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3960step1 raw3960step0; decide +kernel
      have hl : raw3960step1Labels = raw3960step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3960step0 raw3960step0Labels permutation143 permutation3
    mixedMoment B raw3960step1 raw3960step1Labels = mixedMoment B raw3960step2 raw3960step2Labels := by
      have ha : raw3960step2 = -raw3960step1 := by apply Matrix.ext; change ∀ i j, raw3960step2 i j = -(raw3960step1 i j); unfold raw3960step2 raw3960step1; decide +kernel
      have hl : raw3960step2Labels = raw3960step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2465 node2465Labels := by rfl

def raw3961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3961 raw3961Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw3961 raw3961Labels = mixedMoment B raw3961step0 raw3961step0Labels := by
      have hz : ∀ j, raw3961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3961step0 = (fun i j => raw3961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3961step0 raw3961; decide +kernel
      have hl : raw3961step0Labels = raw3961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3961 raw3961Labels permutation346 hz
    mixedMoment B raw3961step0 raw3961step0Labels = mixedMoment B raw3961step1 raw3961step1Labels := by
      have ha : raw3961step1 = (fun i j => raw3961step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3961step1 raw3961step0; decide +kernel
      have hl : raw3961step1Labels = raw3961step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3961step0 raw3961step0Labels permutation44 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw3962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw3962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3962 raw3962Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw3962 raw3962Labels = mixedMoment B raw3962step0 raw3962step0Labels := by
      have hz : ∀ j, raw3962 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3962step0 = (fun i j => raw3962 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3962step0 raw3962; decide +kernel
      have hl : raw3962step0Labels = raw3962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3962 raw3962Labels permutation434 hz
    mixedMoment B raw3962step0 raw3962step0Labels = mixedMoment B raw3962step1 raw3962step1Labels := by
      have hz : ∀ j, raw3962step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3962step1 = (fun i j => raw3962step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3962step1 raw3962step0; decide +kernel
      have hl : raw3962step1Labels = raw3962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3962step0 raw3962step0Labels permutation80 hz
    mixedMoment B raw3962step1 raw3962step1Labels = mixedMoment B raw3962step2 raw3962step2Labels := by
      have ha : raw3962step2 = (fun i j => raw3962step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3962step2 raw3962step1; decide +kernel
      have hl : raw3962step2Labels = raw3962step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3962step1 raw3962step1Labels permutation8 permutation3
    _ = mixedMoment B node1264 node1264Labels := by rfl

def raw3963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3963step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw3963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw3963step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3963 raw3963Labels = mixedMoment B node2640 node2640Labels := by
  calc
    mixedMoment B raw3963 raw3963Labels = mixedMoment B raw3963step0 raw3963step0Labels := by
      have hz : ∀ j, raw3963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3963step0 = (fun i j => raw3963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3963step0 raw3963; decide +kernel
      have hl : raw3963step0Labels = raw3963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3963 raw3963Labels permutation434 hz
    mixedMoment B raw3963step0 raw3963step0Labels = mixedMoment B raw3963step1 raw3963step1Labels := by
      have hz : ∀ j, raw3963step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3963step1 = (fun i j => raw3963step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3963step1 raw3963step0; decide +kernel
      have hl : raw3963step1Labels = raw3963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3963step0 raw3963step0Labels permutation80 hz
    mixedMoment B raw3963step1 raw3963step1Labels = mixedMoment B raw3963step2 raw3963step2Labels := by
      have ha : raw3963step2 = (fun i j => raw3963step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3963step2 raw3963step1; decide +kernel
      have hl : raw3963step2Labels = raw3963step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3963step1 raw3963step1Labels permutation31 permutation3
    mixedMoment B raw3963step2 raw3963step2Labels = mixedMoment B raw3963step3 raw3963step3Labels := by
      have ha : raw3963step3 = -raw3963step2 := by apply Matrix.ext; change ∀ i j, raw3963step3 i j = -(raw3963step2 i j); unfold raw3963step3 raw3963step2; decide +kernel
      have hl : raw3963step3Labels = raw3963step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2640 node2640Labels := by rfl

def raw3964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw3964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw3964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3964 raw3964Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw3964 raw3964Labels = mixedMoment B raw3964step0 raw3964step0Labels := by
      have hz : ∀ j, raw3964 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3964step0 = (fun i j => raw3964 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3964step0 raw3964; decide +kernel
      have hl : raw3964step0Labels = raw3964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3964 raw3964Labels permutation434 hz
    mixedMoment B raw3964step0 raw3964step0Labels = mixedMoment B raw3964step1 raw3964step1Labels := by
      have ha : raw3964step1 = (fun i j => raw3964step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3964step1 raw3964step0; decide +kernel
      have hl : raw3964step1Labels = raw3964step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3964step0 raw3964step0Labels permutation149 permutation3
    mixedMoment B raw3964step1 raw3964step1Labels = mixedMoment B raw3964step2 raw3964step2Labels := by
      have ha : raw3964step2 = -raw3964step1 := by apply Matrix.ext; change ∀ i j, raw3964step2 i j = -(raw3964step1 i j); unfold raw3964step2 raw3964step1; decide +kernel
      have hl : raw3964step2Labels = raw3964step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw3965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw3965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw3965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3965 raw3965Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw3965 raw3965Labels = mixedMoment B raw3965step0 raw3965step0Labels := by
      have hz : ∀ j, raw3965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3965step0 = (fun i j => raw3965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3965step0 raw3965; decide +kernel
      have hl : raw3965step0Labels = raw3965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3965 raw3965Labels permutation346 hz
    mixedMoment B raw3965step0 raw3965step0Labels = mixedMoment B raw3965step1 raw3965step1Labels := by
      have ha : raw3965step1 = (fun i j => raw3965step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3965step1 raw3965step0; decide +kernel
      have hl : raw3965step1Labels = raw3965step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3965step0 raw3965step0Labels permutation149 permutation3
    mixedMoment B raw3965step1 raw3965step1Labels = mixedMoment B raw3965step2 raw3965step2Labels := by
      have ha : raw3965step2 = -raw3965step1 := by apply Matrix.ext; change ∀ i j, raw3965step2 i j = -(raw3965step1 i j); unfold raw3965step2 raw3965step1; decide +kernel
      have hl : raw3965step2Labels = raw3965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw3966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3966step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw3966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3966 raw3966Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw3966 raw3966Labels = mixedMoment B raw3966step0 raw3966step0Labels := by
      have hz : ∀ j, raw3966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3966step0 = (fun i j => raw3966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3966step0 raw3966; decide +kernel
      have hl : raw3966step0Labels = raw3966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3966 raw3966Labels permutation434 hz
    mixedMoment B raw3966step0 raw3966step0Labels = mixedMoment B raw3966step1 raw3966step1Labels := by
      have hz : ∀ j, raw3966step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3966step1 = (fun i j => raw3966step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3966step1 raw3966step0; decide +kernel
      have hl : raw3966step1Labels = raw3966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3966step0 raw3966step0Labels permutation80 hz
    mixedMoment B raw3966step1 raw3966step1Labels = mixedMoment B raw3966step2 raw3966step2Labels := by
      have ha : raw3966step2 = (fun i j => raw3966step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3966step2 raw3966step1; decide +kernel
      have hl : raw3966step2Labels = raw3966step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3966step1 raw3966step1Labels permutation8 permutation3
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw3967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw3967step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-4, 2, 2]]
def raw3967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3967step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw3967step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3967 raw3967Labels = mixedMoment B node994 node994Labels := by
  calc
    mixedMoment B raw3967 raw3967Labels = mixedMoment B raw3967step0 raw3967step0Labels := by
      have hz : ∀ j, raw3967 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3967step0 = (fun i j => raw3967 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3967step0 raw3967; decide +kernel
      have hl : raw3967step0Labels = raw3967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3967 raw3967Labels permutation434 hz
    mixedMoment B raw3967step0 raw3967step0Labels = mixedMoment B raw3967step1 raw3967step1Labels := by
      have hz : ∀ j, raw3967step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3967step1 = (fun i j => raw3967step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3967step1 raw3967step0; decide +kernel
      have hl : raw3967step1Labels = raw3967step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3967step0 raw3967step0Labels permutation80 hz
    mixedMoment B raw3967step1 raw3967step1Labels = mixedMoment B raw3967step2 raw3967step2Labels := by
      have ha : raw3967step2 = (fun i j => raw3967step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3967step2 raw3967step1; decide +kernel
      have hl : raw3967step2Labels = raw3967step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3967step1 raw3967step1Labels permutation29 permutation3
    mixedMoment B raw3967step2 raw3967step2Labels = mixedMoment B raw3967step3 raw3967step3Labels := by
      have ha : raw3967step3 = -raw3967step2 := by apply Matrix.ext; change ∀ i j, raw3967step3 i j = -(raw3967step2 i j); unfold raw3967step3 raw3967step2; decide +kernel
      have hl : raw3967step3Labels = raw3967step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node994 node994Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
