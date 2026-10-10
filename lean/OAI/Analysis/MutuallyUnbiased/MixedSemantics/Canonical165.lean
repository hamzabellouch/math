import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21120 raw21120Labels = mixedMoment B node1017 node1017Labels := by
  calc
    mixedMoment B raw21120 raw21120Labels = mixedMoment B raw21120step0 raw21120step0Labels := by
      have ha : raw21120step0 = (fun i j => raw21120 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21120step0 raw21120; decide +kernel
      have hl : raw21120step0Labels = raw21120Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21120 raw21120Labels permutation154 permutation2
    _ = mixedMoment B node1017 node1017Labels := by rfl

def raw21121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw21121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw21121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21121 raw21121Labels = mixedMoment B node1025 node1025Labels := by
  calc
    mixedMoment B raw21121 raw21121Labels = mixedMoment B raw21121step0 raw21121step0Labels := by
      have hz : ∀ j, raw21121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21121step0 = (fun i j => raw21121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21121step0 raw21121; decide +kernel
      have hl : raw21121step0Labels = raw21121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21121 raw21121Labels permutation434 hz
    _ = mixedMoment B node1025 node1025Labels := by rfl

def raw21122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21122 raw21122Labels = mixedMoment B node972 node972Labels := by
  calc
    mixedMoment B raw21122 raw21122Labels = mixedMoment B raw21122step0 raw21122step0Labels := by
      have ha : raw21122step0 = (fun i j => raw21122 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21122step0 raw21122; decide +kernel
      have hl : raw21122step0Labels = raw21122Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21122 raw21122Labels permutation200 permutation2
    _ = mixedMoment B node972 node972Labels := by rfl

def raw21123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21123 raw21123Labels = mixedMoment B node2071 node2071Labels := by
  calc
    mixedMoment B raw21123 raw21123Labels = mixedMoment B raw21123step0 raw21123step0Labels := by
      have ha : raw21123step0 = (fun i j => raw21123 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21123step0 raw21123; decide +kernel
      have hl : raw21123step0Labels = raw21123Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21123 raw21123Labels permutation158 permutation2
    _ = mixedMoment B node2071 node2071Labels := by rfl

def raw21124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21124 raw21124Labels = mixedMoment B node2071 node2071Labels := by
  calc
    mixedMoment B raw21124 raw21124Labels = mixedMoment B raw21124step0 raw21124step0Labels := by
      have ha : raw21124step0 = (fun i j => raw21124 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21124step0 raw21124; decide +kernel
      have hl : raw21124step0Labels = raw21124Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21124 raw21124Labels permutation182 permutation2
    _ = mixedMoment B node2071 node2071Labels := by rfl

def raw21125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21125 raw21125Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw21125 raw21125Labels = mixedMoment B raw21125step0 raw21125step0Labels := by
      have ha : raw21125step0 = (fun i j => raw21125 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21125step0 raw21125; decide +kernel
      have hl : raw21125step0Labels = raw21125Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21125 raw21125Labels permutation200 permutation2
    _ = mixedMoment B node1898 node1898Labels := by rfl

def raw21126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw21126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw21126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21126 raw21126Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw21126 raw21126Labels = mixedMoment B raw21126step0 raw21126step0Labels := by
      have ha : raw21126step0 = (fun i j => raw21126 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21126step0 raw21126; decide +kernel
      have hl : raw21126step0Labels = raw21126Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21126 raw21126Labels permutation200 permutation2
    _ = mixedMoment B node2187 node2187Labels := by rfl

def raw21127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21127 raw21127Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw21127 raw21127Labels = mixedMoment B raw21127step0 raw21127step0Labels := by
      have ha : raw21127step0 = (fun i j => raw21127 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21127step0 raw21127; decide +kernel
      have hl : raw21127step0Labels = raw21127Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21127 raw21127Labels permutation200 permutation2
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw21128 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw21128Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21128step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw21128step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21128 raw21128Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw21128 raw21128Labels = mixedMoment B raw21128step0 raw21128step0Labels := by
      have ha : raw21128step0 = (fun i j => raw21128 (permutation200 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21128step0 raw21128; decide +kernel
      have hl : raw21128step0Labels = raw21128Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21128 raw21128Labels permutation200 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw21129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21129 raw21129Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw21129 raw21129Labels = mixedMoment B raw21129step0 raw21129step0Labels := by
      have ha : raw21129step0 = (fun i j => raw21129 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21129step0 raw21129; decide +kernel
      have hl : raw21129step0Labels = raw21129Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21129 raw21129Labels permutation206 permutation2
    _ = mixedMoment B node980 node980Labels := by rfl

def raw21130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21130step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21130 raw21130Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw21130 raw21130Labels = mixedMoment B raw21130step0 raw21130step0Labels := by
      have ha : raw21130step0 = (fun i j => raw21130 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21130step0 raw21130; decide +kernel
      have hl : raw21130step0Labels = raw21130Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21130 raw21130Labels permutation200 permutation2
    _ = mixedMoment B node980 node980Labels := by rfl

def raw21131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21131 raw21131Labels = mixedMoment B node1018 node1018Labels := by
  calc
    _ = mixedMoment B node1018 node1018Labels := by rfl

def raw21132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw21132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw21132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21132 raw21132Labels = mixedMoment B node974 node974Labels := by
  calc
    mixedMoment B raw21132 raw21132Labels = mixedMoment B raw21132step0 raw21132step0Labels := by
      have ha : raw21132step0 = (fun i j => raw21132 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21132step0 raw21132; decide +kernel
      have hl : raw21132step0Labels = raw21132Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21132 raw21132Labels permutation200 permutation2
    _ = mixedMoment B node974 node974Labels := by rfl

def raw21133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21133 raw21133Labels = mixedMoment B node971 node971Labels := by
  calc
    mixedMoment B raw21133 raw21133Labels = mixedMoment B raw21133step0 raw21133step0Labels := by
      have ha : raw21133step0 = (fun i j => raw21133 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21133step0 raw21133; decide +kernel
      have hl : raw21133step0Labels = raw21133Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21133 raw21133Labels permutation200 permutation2
    _ = mixedMoment B node971 node971Labels := by rfl

def raw21134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21134 raw21134Labels = mixedMoment B node2070 node2070Labels := by
  calc
    mixedMoment B raw21134 raw21134Labels = mixedMoment B raw21134step0 raw21134step0Labels := by
      have ha : raw21134step0 = (fun i j => raw21134 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21134step0 raw21134; decide +kernel
      have hl : raw21134step0Labels = raw21134Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21134 raw21134Labels permutation158 permutation2
    _ = mixedMoment B node2070 node2070Labels := by rfl

def raw21135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21135 raw21135Labels = mixedMoment B node2070 node2070Labels := by
  calc
    mixedMoment B raw21135 raw21135Labels = mixedMoment B raw21135step0 raw21135step0Labels := by
      have ha : raw21135step0 = (fun i j => raw21135 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21135step0 raw21135; decide +kernel
      have hl : raw21135step0Labels = raw21135Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21135 raw21135Labels permutation182 permutation2
    _ = mixedMoment B node2070 node2070Labels := by rfl

def raw21136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21136 raw21136Labels = mixedMoment B node1897 node1897Labels := by
  calc
    mixedMoment B raw21136 raw21136Labels = mixedMoment B raw21136step0 raw21136step0Labels := by
      have ha : raw21136step0 = (fun i j => raw21136 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21136step0 raw21136; decide +kernel
      have hl : raw21136step0Labels = raw21136Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21136 raw21136Labels permutation200 permutation2
    _ = mixedMoment B node1897 node1897Labels := by rfl

def raw21137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw21137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw21137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21137 raw21137Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw21137 raw21137Labels = mixedMoment B raw21137step0 raw21137step0Labels := by
      have hz : ∀ j, raw21137 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21137step0 = (fun i j => raw21137 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21137step0 raw21137; decide +kernel
      have hl : raw21137step0Labels = raw21137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21137 raw21137Labels permutation520 hz
    mixedMoment B raw21137step0 raw21137step0Labels = mixedMoment B raw21137step1 raw21137step1Labels := by
      have ha : raw21137step1 = (fun i j => raw21137step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21137step1 raw21137step0; decide +kernel
      have hl : raw21137step1Labels = raw21137step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21137step0 raw21137step0Labels permutation44 permutation2
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw21138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21138 raw21138Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw21138 raw21138Labels = mixedMoment B raw21138step0 raw21138step0Labels := by
      have ha : raw21138step0 = (fun i j => raw21138 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21138step0 raw21138; decide +kernel
      have hl : raw21138step0Labels = raw21138Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21138 raw21138Labels permutation200 permutation2
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw21139 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]
def raw21139Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21139step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2]]
def raw21139step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21139step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw21139step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21139 raw21139Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21139 raw21139Labels = mixedMoment B raw21139step0 raw21139step0Labels := by
      have hz : ∀ j, raw21139 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21139step0 = (fun i j => raw21139 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21139step0 raw21139; decide +kernel
      have hl : raw21139step0Labels = raw21139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21139 raw21139Labels permutation520 hz
    mixedMoment B raw21139step0 raw21139step0Labels = mixedMoment B raw21139step1 raw21139step1Labels := by
      have ha : raw21139step1 = (fun i j => raw21139step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21139step1 raw21139step0; decide +kernel
      have hl : raw21139step1Labels = raw21139step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21139step0 raw21139step0Labels permutation44 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw21140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21140 raw21140Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw21140 raw21140Labels = mixedMoment B raw21140step0 raw21140step0Labels := by
      have ha : raw21140step0 = (fun i j => raw21140 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21140step0 raw21140; decide +kernel
      have hl : raw21140step0Labels = raw21140Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21140 raw21140Labels permutation208 permutation2
    _ = mixedMoment B node977 node977Labels := by rfl

def raw21141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21141Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21141step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21141 raw21141Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw21141 raw21141Labels = mixedMoment B raw21141step0 raw21141step0Labels := by
      have ha : raw21141step0 = (fun i j => raw21141 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21141step0 raw21141; decide +kernel
      have hl : raw21141step0Labels = raw21141Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21141 raw21141Labels permutation202 permutation2
    _ = mixedMoment B node977 node977Labels := by rfl

def raw21142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21142Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21142 raw21142Labels = mixedMoment B node1017 node1017Labels := by
  calc
    _ = mixedMoment B node1017 node1017Labels := by rfl

def raw21143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw21143Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw21143step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21143 raw21143Labels = mixedMoment B node973 node973Labels := by
  calc
    mixedMoment B raw21143 raw21143Labels = mixedMoment B raw21143step0 raw21143step0Labels := by
      have ha : raw21143step0 = (fun i j => raw21143 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21143step0 raw21143; decide +kernel
      have hl : raw21143step0Labels = raw21143Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21143 raw21143Labels permutation200 permutation2
    _ = mixedMoment B node973 node973Labels := by rfl

def raw21144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21144 raw21144Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw21144 raw21144Labels = mixedMoment B raw21144step0 raw21144step0Labels := by
      have hz : ∀ j, raw21144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21144step0 = (fun i j => raw21144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21144step0 raw21144; decide +kernel
      have hl : raw21144step0Labels = raw21144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21144 raw21144Labels permutation434 hz
    mixedMoment B raw21144step0 raw21144step0Labels = mixedMoment B raw21144step1 raw21144step1Labels := by
      have hz : ∀ j, raw21144step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21144step1 = (fun i j => raw21144step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21144step1 raw21144step0; decide +kernel
      have hl : raw21144step1Labels = raw21144step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21144step0 raw21144step0Labels permutation80 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw21145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21145 raw21145Labels = mixedMoment B node4183 node4183Labels := by
  calc
    mixedMoment B raw21145 raw21145Labels = mixedMoment B raw21145step0 raw21145step0Labels := by
      have hz : ∀ j, raw21145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21145step0 = (fun i j => raw21145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21145step0 raw21145; decide +kernel
      have hl : raw21145step0Labels = raw21145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21145 raw21145Labels permutation434 hz
    mixedMoment B raw21145step0 raw21145step0Labels = mixedMoment B raw21145step1 raw21145step1Labels := by
      have hz : ∀ j, raw21145step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21145step1 = (fun i j => raw21145step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21145step1 raw21145step0; decide +kernel
      have hl : raw21145step1Labels = raw21145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21145step0 raw21145step0Labels permutation80 hz
    _ = mixedMoment B node4183 node4183Labels := by rfl

def raw21146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21146 raw21146Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw21146 raw21146Labels = mixedMoment B raw21146step0 raw21146step0Labels := by
      have hz : ∀ j, raw21146 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21146step0 = (fun i j => raw21146 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21146step0 raw21146; decide +kernel
      have hl : raw21146step0Labels = raw21146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21146 raw21146Labels permutation434 hz
    mixedMoment B raw21146step0 raw21146step0Labels = mixedMoment B raw21146step1 raw21146step1Labels := by
      have ha : raw21146step1 = (fun i j => raw21146step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21146step1 raw21146step0; decide +kernel
      have hl : raw21146step1Labels = raw21146step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21146step0 raw21146step0Labels permutation38 permutation2
    _ = mixedMoment B node4352 node4352Labels := by rfl

def raw21147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21147 raw21147Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw21147 raw21147Labels = mixedMoment B raw21147step0 raw21147step0Labels := by
      have hz : ∀ j, raw21147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21147step0 = (fun i j => raw21147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21147step0 raw21147; decide +kernel
      have hl : raw21147step0Labels = raw21147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21147 raw21147Labels permutation346 hz
    mixedMoment B raw21147step0 raw21147step0Labels = mixedMoment B raw21147step1 raw21147step1Labels := by
      have ha : raw21147step1 = (fun i j => raw21147step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21147step1 raw21147step0; decide +kernel
      have hl : raw21147step1Labels = raw21147step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21147step0 raw21147step0Labels permutation38 permutation2
    _ = mixedMoment B node4352 node4352Labels := by rfl

def raw21148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw21148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21148 raw21148Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21148 raw21148Labels = mixedMoment B raw21148step0 raw21148step0Labels := by
      have hz : ∀ j, raw21148 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21148step0 = (fun i j => raw21148 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21148step0 raw21148; decide +kernel
      have hl : raw21148step0Labels = raw21148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21148 raw21148Labels permutation434 hz
    mixedMoment B raw21148step0 raw21148step0Labels = mixedMoment B raw21148step1 raw21148step1Labels := by
      have hz : ∀ j, raw21148step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21148step1 = (fun i j => raw21148step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21148step1 raw21148step0; decide +kernel
      have hl : raw21148step1Labels = raw21148step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21148step0 raw21148step0Labels permutation80 hz
    mixedMoment B raw21148step1 raw21148step1Labels = mixedMoment B raw21148step2 raw21148step2Labels := by
      have ha : raw21148step2 = (fun i j => raw21148step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21148step2 raw21148step1; decide +kernel
      have hl : raw21148step2Labels = raw21148step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21148step1 raw21148step1Labels permutation10 permutation2
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw21149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21149 raw21149Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw21149 raw21149Labels = mixedMoment B raw21149step0 raw21149step0Labels := by
      have hz : ∀ j, raw21149 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21149step0 = (fun i j => raw21149 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21149step0 raw21149; decide +kernel
      have hl : raw21149step0Labels = raw21149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21149 raw21149Labels permutation434 hz
    _ = mixedMoment B node4153 node4153Labels := by rfl

def raw21150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21150 raw21150Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw21150 raw21150Labels = mixedMoment B raw21150step0 raw21150step0Labels := by
      have hz : ∀ j, raw21150 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21150step0 = (fun i j => raw21150 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21150step0 raw21150; decide +kernel
      have hl : raw21150step0Labels = raw21150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21150 raw21150Labels permutation434 hz
    _ = mixedMoment B node4367 node4367Labels := by rfl

def raw21151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21151 raw21151Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw21151 raw21151Labels = mixedMoment B raw21151step0 raw21151step0Labels := by
      have ha : raw21151step0 = (fun i j => raw21151 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21151step0 raw21151; decide +kernel
      have hl : raw21151step0Labels = raw21151Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21151 raw21151Labels permutation200 permutation2
    _ = mixedMoment B node4327 node4327Labels := by rfl

def raw21152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21152 raw21152Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw21152 raw21152Labels = mixedMoment B raw21152step0 raw21152step0Labels := by
      have hz : ∀ j, raw21152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21152step0 = (fun i j => raw21152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21152step0 raw21152; decide +kernel
      have hl : raw21152step0Labels = raw21152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21152 raw21152Labels permutation434 hz
    mixedMoment B raw21152step0 raw21152step0Labels = mixedMoment B raw21152step1 raw21152step1Labels := by
      have ha : raw21152step1 = (fun i j => raw21152step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21152step1 raw21152step0; decide +kernel
      have hl : raw21152step1Labels = raw21152step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21152step0 raw21152step0Labels permutation34 permutation2
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw21153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21153 raw21153Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw21153 raw21153Labels = mixedMoment B raw21153step0 raw21153step0Labels := by
      have hz : ∀ j, raw21153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21153step0 = (fun i j => raw21153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21153step0 raw21153; decide +kernel
      have hl : raw21153step0Labels = raw21153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21153 raw21153Labels permutation346 hz
    _ = mixedMoment B node4153 node4153Labels := by rfl

def raw21154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21154 raw21154Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw21154 raw21154Labels = mixedMoment B raw21154step0 raw21154step0Labels := by
      have hz : ∀ j, raw21154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21154step0 = (fun i j => raw21154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21154step0 raw21154; decide +kernel
      have hl : raw21154step0Labels = raw21154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21154 raw21154Labels permutation346 hz
    _ = mixedMoment B node4367 node4367Labels := by rfl

def raw21155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21155 raw21155Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw21155 raw21155Labels = mixedMoment B raw21155step0 raw21155step0Labels := by
      have ha : raw21155step0 = (fun i j => raw21155 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21155step0 raw21155; decide +kernel
      have hl : raw21155step0Labels = raw21155Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21155 raw21155Labels permutation176 permutation2
    _ = mixedMoment B node4327 node4327Labels := by rfl

def raw21156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21156 raw21156Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw21156 raw21156Labels = mixedMoment B raw21156step0 raw21156step0Labels := by
      have hz : ∀ j, raw21156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21156step0 = (fun i j => raw21156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21156step0 raw21156; decide +kernel
      have hl : raw21156step0Labels = raw21156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21156 raw21156Labels permutation346 hz
    mixedMoment B raw21156step0 raw21156step0Labels = mixedMoment B raw21156step1 raw21156step1Labels := by
      have ha : raw21156step1 = (fun i j => raw21156step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21156step1 raw21156step0; decide +kernel
      have hl : raw21156step1Labels = raw21156step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21156step0 raw21156step0Labels permutation34 permutation2
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw21157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21157 raw21157Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw21157 raw21157Labels = mixedMoment B raw21157step0 raw21157step0Labels := by
      have hz : ∀ j, raw21157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21157step0 = (fun i j => raw21157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21157step0 raw21157; decide +kernel
      have hl : raw21157step0Labels = raw21157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21157 raw21157Labels permutation434 hz
    mixedMoment B raw21157step0 raw21157step0Labels = mixedMoment B raw21157step1 raw21157step1Labels := by
      have hz : ∀ j, raw21157step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21157step1 = (fun i j => raw21157step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21157step1 raw21157step0; decide +kernel
      have hl : raw21157step1Labels = raw21157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21157step0 raw21157step0Labels permutation80 hz
    _ = mixedMoment B node4161 node4161Labels := by rfl

def raw21158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21158 raw21158Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw21158 raw21158Labels = mixedMoment B raw21158step0 raw21158step0Labels := by
      have hz : ∀ j, raw21158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21158step0 = (fun i j => raw21158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21158step0 raw21158; decide +kernel
      have hl : raw21158step0Labels = raw21158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21158 raw21158Labels permutation434 hz
    mixedMoment B raw21158step0 raw21158step0Labels = mixedMoment B raw21158step1 raw21158step1Labels := by
      have hz : ∀ j, raw21158step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21158step1 = (fun i j => raw21158step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21158step1 raw21158step0; decide +kernel
      have hl : raw21158step1Labels = raw21158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21158step0 raw21158step0Labels permutation80 hz
    _ = mixedMoment B node4374 node4374Labels := by rfl

def raw21159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21159 raw21159Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw21159 raw21159Labels = mixedMoment B raw21159step0 raw21159step0Labels := by
      have hz : ∀ j, raw21159 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21159step0 = (fun i j => raw21159 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21159step0 raw21159; decide +kernel
      have hl : raw21159step0Labels = raw21159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21159 raw21159Labels permutation434 hz
    mixedMoment B raw21159step0 raw21159step0Labels = mixedMoment B raw21159step1 raw21159step1Labels := by
      have ha : raw21159step1 = (fun i j => raw21159step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21159step1 raw21159step0; decide +kernel
      have hl : raw21159step1Labels = raw21159step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21159step0 raw21159step0Labels permutation38 permutation2
    _ = mixedMoment B node4335 node4335Labels := by rfl

def raw21160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21160 raw21160Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw21160 raw21160Labels = mixedMoment B raw21160step0 raw21160step0Labels := by
      have hz : ∀ j, raw21160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21160step0 = (fun i j => raw21160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21160step0 raw21160; decide +kernel
      have hl : raw21160step0Labels = raw21160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21160 raw21160Labels permutation346 hz
    mixedMoment B raw21160step0 raw21160step0Labels = mixedMoment B raw21160step1 raw21160step1Labels := by
      have ha : raw21160step1 = (fun i j => raw21160step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21160step1 raw21160step0; decide +kernel
      have hl : raw21160step1Labels = raw21160step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21160step0 raw21160step0Labels permutation38 permutation2
    _ = mixedMoment B node4335 node4335Labels := by rfl

def raw21161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21161 raw21161Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw21161 raw21161Labels = mixedMoment B raw21161step0 raw21161step0Labels := by
      have hz : ∀ j, raw21161 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21161step0 = (fun i j => raw21161 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21161step0 raw21161; decide +kernel
      have hl : raw21161step0Labels = raw21161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21161 raw21161Labels permutation434 hz
    mixedMoment B raw21161step0 raw21161step0Labels = mixedMoment B raw21161step1 raw21161step1Labels := by
      have hz : ∀ j, raw21161step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21161step1 = (fun i j => raw21161step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21161step1 raw21161step0; decide +kernel
      have hl : raw21161step1Labels = raw21161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21161step0 raw21161step0Labels permutation80 hz
    _ = mixedMoment B node4159 node4159Labels := by rfl

def raw21162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21162step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21162step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, -1, 2], ![-4, 3, 1]]
def raw21162step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21162step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21162step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21162step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21162step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21162 raw21162Labels = mixedMoment B node4358 node4358Labels := by
  calc
    mixedMoment B raw21162 raw21162Labels = mixedMoment B raw21162step0 raw21162step0Labels := by
      have hz : ∀ j, raw21162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21162step0 = (fun i j => raw21162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21162step0 raw21162; decide +kernel
      have hl : raw21162step0Labels = raw21162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21162 raw21162Labels permutation434 hz
    mixedMoment B raw21162step0 raw21162step0Labels = mixedMoment B raw21162step1 raw21162step1Labels := by
      have hz : ∀ j, raw21162step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21162step1 = (fun i j => raw21162step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21162step1 raw21162step0; decide +kernel
      have hl : raw21162step1Labels = raw21162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21162step0 raw21162step0Labels permutation80 hz
    mixedMoment B raw21162step1 raw21162step1Labels = mixedMoment B raw21162step2 raw21162step2Labels := by
      have ha : raw21162step2 = (fun i j => raw21162step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21162step2 raw21162step1; decide +kernel
      have hl : raw21162step2Labels = raw21162step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21162step1 raw21162step1Labels permutation31 permutation3
    mixedMoment B raw21162step2 raw21162step2Labels = mixedMoment B raw21162step3 raw21162step3Labels := by
      have ha : raw21162step3 = -raw21162step2 := by apply Matrix.ext; change ∀ i j, raw21162step3 i j = -(raw21162step2 i j); unfold raw21162step3 raw21162step2; decide +kernel
      have hl : raw21162step3Labels = raw21162step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21162step3 raw21162step3Labels = mixedMoment B raw21162step4 raw21162step4Labels := by
      have ha : raw21162step4 = raw21162step3 := by apply Matrix.ext; unfold raw21162step4 raw21162step3; decide +kernel
      have hl : raw21162step3Labels = labelEmbedding6 ∘ raw21162step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21162step3 raw21162step3Labels raw21162step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4358 node4358Labels := by rfl

def raw21163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21163 raw21163Labels = mixedMoment B node4333 node4333Labels := by
  calc
    mixedMoment B raw21163 raw21163Labels = mixedMoment B raw21163step0 raw21163step0Labels := by
      have hz : ∀ j, raw21163 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21163step0 = (fun i j => raw21163 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21163step0 raw21163; decide +kernel
      have hl : raw21163step0Labels = raw21163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21163 raw21163Labels permutation434 hz
    mixedMoment B raw21163step0 raw21163step0Labels = mixedMoment B raw21163step1 raw21163step1Labels := by
      have ha : raw21163step1 = (fun i j => raw21163step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21163step1 raw21163step0; decide +kernel
      have hl : raw21163step1Labels = raw21163step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21163step0 raw21163step0Labels permutation38 permutation2
    _ = mixedMoment B node4333 node4333Labels := by rfl

def raw21164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21164step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21164 raw21164Labels = mixedMoment B node4333 node4333Labels := by
  calc
    mixedMoment B raw21164 raw21164Labels = mixedMoment B raw21164step0 raw21164step0Labels := by
      have hz : ∀ j, raw21164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21164step0 = (fun i j => raw21164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21164step0 raw21164; decide +kernel
      have hl : raw21164step0Labels = raw21164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21164 raw21164Labels permutation346 hz
    mixedMoment B raw21164step0 raw21164step0Labels = mixedMoment B raw21164step1 raw21164step1Labels := by
      have ha : raw21164step1 = (fun i j => raw21164step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21164step1 raw21164step0; decide +kernel
      have hl : raw21164step1Labels = raw21164step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21164step0 raw21164step0Labels permutation38 permutation2
    _ = mixedMoment B node4333 node4333Labels := by rfl

def raw21165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw21165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw21165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw21165step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21165 raw21165Labels = mixedMoment B node4445 node4445Labels := by
  calc
    mixedMoment B raw21165 raw21165Labels = mixedMoment B raw21165step0 raw21165step0Labels := by
      have hz : ∀ j, raw21165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21165step0 = (fun i j => raw21165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21165step0 raw21165; decide +kernel
      have hl : raw21165step0Labels = raw21165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21165 raw21165Labels permutation434 hz
    mixedMoment B raw21165step0 raw21165step0Labels = mixedMoment B raw21165step1 raw21165step1Labels := by
      have hz : ∀ j, raw21165step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21165step1 = (fun i j => raw21165step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21165step1 raw21165step0; decide +kernel
      have hl : raw21165step1Labels = raw21165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21165step0 raw21165step0Labels permutation80 hz
    _ = mixedMoment B node4445 node4445Labels := by rfl

def raw21166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21166step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, -1, 2], ![-3, 3, 0]]
def raw21166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21166step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw21166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21166 raw21166Labels = mixedMoment B node2602 node2602Labels := by
  calc
    mixedMoment B raw21166 raw21166Labels = mixedMoment B raw21166step0 raw21166step0Labels := by
      have hz : ∀ j, raw21166 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21166step0 = (fun i j => raw21166 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21166step0 raw21166; decide +kernel
      have hl : raw21166step0Labels = raw21166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21166 raw21166Labels permutation434 hz
    mixedMoment B raw21166step0 raw21166step0Labels = mixedMoment B raw21166step1 raw21166step1Labels := by
      have hz : ∀ j, raw21166step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21166step1 = (fun i j => raw21166step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21166step1 raw21166step0; decide +kernel
      have hl : raw21166step1Labels = raw21166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21166step0 raw21166step0Labels permutation80 hz
    mixedMoment B raw21166step1 raw21166step1Labels = mixedMoment B raw21166step2 raw21166step2Labels := by
      have ha : raw21166step2 = (fun i j => raw21166step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21166step2 raw21166step1; decide +kernel
      have hl : raw21166step2Labels = raw21166step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21166step1 raw21166step1Labels permutation31 permutation3
    mixedMoment B raw21166step2 raw21166step2Labels = mixedMoment B raw21166step3 raw21166step3Labels := by
      have ha : raw21166step3 = -raw21166step2 := by apply Matrix.ext; change ∀ i j, raw21166step3 i j = -(raw21166step2 i j); unfold raw21166step3 raw21166step2; decide +kernel
      have hl : raw21166step3Labels = raw21166step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2602 node2602Labels := by rfl

def raw21167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw21167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21167 raw21167Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw21167 raw21167Labels = mixedMoment B raw21167step0 raw21167step0Labels := by
      have hz : ∀ j, raw21167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21167step0 = (fun i j => raw21167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21167step0 raw21167; decide +kernel
      have hl : raw21167step0Labels = raw21167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21167 raw21167Labels permutation434 hz
    mixedMoment B raw21167step0 raw21167step0Labels = mixedMoment B raw21167step1 raw21167step1Labels := by
      have ha : raw21167step1 = (fun i j => raw21167step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21167step1 raw21167step0; decide +kernel
      have hl : raw21167step1Labels = raw21167step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21167step0 raw21167step0Labels permutation149 permutation3
    mixedMoment B raw21167step1 raw21167step1Labels = mixedMoment B raw21167step2 raw21167step2Labels := by
      have ha : raw21167step2 = -raw21167step1 := by apply Matrix.ext; change ∀ i j, raw21167step2 i j = -(raw21167step1 i j); unfold raw21167step2 raw21167step1; decide +kernel
      have hl : raw21167step2Labels = raw21167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw21168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw21168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21168 raw21168Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw21168 raw21168Labels = mixedMoment B raw21168step0 raw21168step0Labels := by
      have hz : ∀ j, raw21168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21168step0 = (fun i j => raw21168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21168step0 raw21168; decide +kernel
      have hl : raw21168step0Labels = raw21168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21168 raw21168Labels permutation346 hz
    mixedMoment B raw21168step0 raw21168step0Labels = mixedMoment B raw21168step1 raw21168step1Labels := by
      have ha : raw21168step1 = (fun i j => raw21168step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21168step1 raw21168step0; decide +kernel
      have hl : raw21168step1Labels = raw21168step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21168step0 raw21168step0Labels permutation149 permutation3
    mixedMoment B raw21168step1 raw21168step1Labels = mixedMoment B raw21168step2 raw21168step2Labels := by
      have ha : raw21168step2 = -raw21168step1 := by apply Matrix.ext; change ∀ i j, raw21168step2 i j = -(raw21168step1 i j); unfold raw21168step2 raw21168step1; decide +kernel
      have hl : raw21168step2Labels = raw21168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw21169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw21169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw21169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21169step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw21169step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21169 raw21169Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw21169 raw21169Labels = mixedMoment B raw21169step0 raw21169step0Labels := by
      have hz : ∀ j, raw21169 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21169step0 = (fun i j => raw21169 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21169step0 raw21169; decide +kernel
      have hl : raw21169step0Labels = raw21169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21169 raw21169Labels permutation434 hz
    mixedMoment B raw21169step0 raw21169step0Labels = mixedMoment B raw21169step1 raw21169step1Labels := by
      have hz : ∀ j, raw21169step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21169step1 = (fun i j => raw21169step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21169step1 raw21169step0; decide +kernel
      have hl : raw21169step1Labels = raw21169step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21169step0 raw21169step0Labels permutation80 hz
    mixedMoment B raw21169step1 raw21169step1Labels = mixedMoment B raw21169step2 raw21169step2Labels := by
      have ha : raw21169step2 = (fun i j => raw21169step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21169step2 raw21169step1; decide +kernel
      have hl : raw21169step2Labels = raw21169step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21169step1 raw21169step1Labels permutation29 permutation3
    mixedMoment B raw21169step2 raw21169step2Labels = mixedMoment B raw21169step3 raw21169step3Labels := by
      have ha : raw21169step3 = -raw21169step2 := by apply Matrix.ext; change ∀ i j, raw21169step3 i j = -(raw21169step2 i j); unfold raw21169step3 raw21169step2; decide +kernel
      have hl : raw21169step3Labels = raw21169step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw21170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21170step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw21170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21170 raw21170Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw21170 raw21170Labels = mixedMoment B raw21170step0 raw21170step0Labels := by
      have hz : ∀ j, raw21170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21170step0 = (fun i j => raw21170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21170step0 raw21170; decide +kernel
      have hl : raw21170step0Labels = raw21170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21170 raw21170Labels permutation434 hz
    mixedMoment B raw21170step0 raw21170step0Labels = mixedMoment B raw21170step1 raw21170step1Labels := by
      have hz : ∀ j, raw21170step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21170step1 = (fun i j => raw21170step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21170step1 raw21170step0; decide +kernel
      have hl : raw21170step1Labels = raw21170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21170step0 raw21170step0Labels permutation80 hz
    mixedMoment B raw21170step1 raw21170step1Labels = mixedMoment B raw21170step2 raw21170step2Labels := by
      have ha : raw21170step2 = (fun i j => raw21170step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21170step2 raw21170step1; decide +kernel
      have hl : raw21170step2Labels = raw21170step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21170step1 raw21170step1Labels permutation8 permutation3
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw21171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21171step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21171step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21171 raw21171Labels = mixedMoment B node645 node645Labels := by
  calc
    mixedMoment B raw21171 raw21171Labels = mixedMoment B raw21171step0 raw21171step0Labels := by
      have hz : ∀ j, raw21171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21171step0 = (fun i j => raw21171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21171step0 raw21171; decide +kernel
      have hl : raw21171step0Labels = raw21171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21171 raw21171Labels permutation434 hz
    mixedMoment B raw21171step0 raw21171step0Labels = mixedMoment B raw21171step1 raw21171step1Labels := by
      have hz : ∀ j, raw21171step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21171step1 = (fun i j => raw21171step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21171step1 raw21171step0; decide +kernel
      have hl : raw21171step1Labels = raw21171step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21171step0 raw21171step0Labels permutation80 hz
    mixedMoment B raw21171step1 raw21171step1Labels = mixedMoment B raw21171step2 raw21171step2Labels := by
      have ha : raw21171step2 = (fun i j => raw21171step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21171step2 raw21171step1; decide +kernel
      have hl : raw21171step2Labels = raw21171step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21171step1 raw21171step1Labels permutation8 permutation3
    _ = mixedMoment B node645 node645Labels := by rfl

def raw21172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21172 raw21172Labels = mixedMoment B node1340 node1340Labels := by
  calc
    mixedMoment B raw21172 raw21172Labels = mixedMoment B raw21172step0 raw21172step0Labels := by
      have hz : ∀ j, raw21172 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21172step0 = (fun i j => raw21172 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21172step0 raw21172; decide +kernel
      have hl : raw21172step0Labels = raw21172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21172 raw21172Labels permutation434 hz
    mixedMoment B raw21172step0 raw21172step0Labels = mixedMoment B raw21172step1 raw21172step1Labels := by
      have ha : raw21172step1 = (fun i j => raw21172step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21172step1 raw21172step0; decide +kernel
      have hl : raw21172step1Labels = raw21172step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21172step0 raw21172step0Labels permutation38 permutation3
    _ = mixedMoment B node1340 node1340Labels := by rfl

def raw21173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21173 raw21173Labels = mixedMoment B node1340 node1340Labels := by
  calc
    mixedMoment B raw21173 raw21173Labels = mixedMoment B raw21173step0 raw21173step0Labels := by
      have hz : ∀ j, raw21173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21173step0 = (fun i j => raw21173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21173step0 raw21173; decide +kernel
      have hl : raw21173step0Labels = raw21173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21173 raw21173Labels permutation346 hz
    mixedMoment B raw21173step0 raw21173step0Labels = mixedMoment B raw21173step1 raw21173step1Labels := by
      have ha : raw21173step1 = (fun i j => raw21173step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21173step1 raw21173step0; decide +kernel
      have hl : raw21173step1Labels = raw21173step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21173step0 raw21173step0Labels permutation38 permutation3
    _ = mixedMoment B node1340 node1340Labels := by rfl

def raw21174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw21174step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21174step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21174 raw21174Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw21174 raw21174Labels = mixedMoment B raw21174step0 raw21174step0Labels := by
      have hz : ∀ j, raw21174 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21174step0 = (fun i j => raw21174 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21174step0 raw21174; decide +kernel
      have hl : raw21174step0Labels = raw21174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21174 raw21174Labels permutation434 hz
    mixedMoment B raw21174step0 raw21174step0Labels = mixedMoment B raw21174step1 raw21174step1Labels := by
      have hz : ∀ j, raw21174step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21174step1 = (fun i j => raw21174step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21174step1 raw21174step0; decide +kernel
      have hl : raw21174step1Labels = raw21174step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21174step0 raw21174step0Labels permutation80 hz
    mixedMoment B raw21174step1 raw21174step1Labels = mixedMoment B raw21174step2 raw21174step2Labels := by
      have ha : raw21174step2 = (fun i j => raw21174step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21174step2 raw21174step1; decide +kernel
      have hl : raw21174step2Labels = raw21174step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21174step1 raw21174step1Labels permutation10 permutation3
    _ = mixedMoment B node1413 node1413Labels := by rfl

def raw21175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21175step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21175step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw21175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21175 raw21175Labels = mixedMoment B node1447 node1447Labels := by
  calc
    mixedMoment B raw21175 raw21175Labels = mixedMoment B raw21175step0 raw21175step0Labels := by
      have hz : ∀ j, raw21175 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21175step0 = (fun i j => raw21175 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21175step0 raw21175; decide +kernel
      have hl : raw21175step0Labels = raw21175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21175 raw21175Labels permutation434 hz
    mixedMoment B raw21175step0 raw21175step0Labels = mixedMoment B raw21175step1 raw21175step1Labels := by
      have hz : ∀ j, raw21175step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21175step1 = (fun i j => raw21175step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21175step1 raw21175step0; decide +kernel
      have hl : raw21175step1Labels = raw21175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21175step0 raw21175step0Labels permutation80 hz
    mixedMoment B raw21175step1 raw21175step1Labels = mixedMoment B raw21175step2 raw21175step2Labels := by
      have ha : raw21175step2 = (fun i j => raw21175step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21175step2 raw21175step1; decide +kernel
      have hl : raw21175step2Labels = raw21175step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21175step1 raw21175step1Labels permutation8 permutation3
    _ = mixedMoment B node1447 node1447Labels := by rfl

def raw21176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21176 raw21176Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw21176 raw21176Labels = mixedMoment B raw21176step0 raw21176step0Labels := by
      have hz : ∀ j, raw21176 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21176step0 = (fun i j => raw21176 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21176step0 raw21176; decide +kernel
      have hl : raw21176step0Labels = raw21176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21176 raw21176Labels permutation434 hz
    mixedMoment B raw21176step0 raw21176step0Labels = mixedMoment B raw21176step1 raw21176step1Labels := by
      have ha : raw21176step1 = (fun i j => raw21176step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21176step1 raw21176step0; decide +kernel
      have hl : raw21176step1Labels = raw21176step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21176step0 raw21176step0Labels permutation34 permutation3
    _ = mixedMoment B node626 node626Labels := by rfl

def raw21177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21177 raw21177Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw21177 raw21177Labels = mixedMoment B raw21177step0 raw21177step0Labels := by
      have hz : ∀ j, raw21177 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21177step0 = (fun i j => raw21177 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21177step0 raw21177; decide +kernel
      have hl : raw21177step0Labels = raw21177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21177 raw21177Labels permutation434 hz
    mixedMoment B raw21177step0 raw21177step0Labels = mixedMoment B raw21177step1 raw21177step1Labels := by
      have ha : raw21177step1 = (fun i j => raw21177step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21177step1 raw21177step0; decide +kernel
      have hl : raw21177step1Labels = raw21177step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21177step0 raw21177step0Labels permutation34 permutation3
    _ = mixedMoment B node1317 node1317Labels := by rfl

def raw21178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21178 raw21178Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw21178 raw21178Labels = mixedMoment B raw21178step0 raw21178step0Labels := by
      have ha : raw21178step0 = (fun i j => raw21178 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21178step0 raw21178; decide +kernel
      have hl : raw21178step0Labels = raw21178Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21178 raw21178Labels permutation202 permutation3
    _ = mixedMoment B node1327 node1327Labels := by rfl

def raw21179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21179step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21179 raw21179Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw21179 raw21179Labels = mixedMoment B raw21179step0 raw21179step0Labels := by
      have hz : ∀ j, raw21179 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21179step0 = (fun i j => raw21179 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21179step0 raw21179; decide +kernel
      have hl : raw21179step0Labels = raw21179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21179 raw21179Labels permutation434 hz
    mixedMoment B raw21179step0 raw21179step0Labels = mixedMoment B raw21179step1 raw21179step1Labels := by
      have ha : raw21179step1 = (fun i j => raw21179step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21179step1 raw21179step0; decide +kernel
      have hl : raw21179step1Labels = raw21179step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21179step0 raw21179step0Labels permutation34 permutation3
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw21180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21180 raw21180Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw21180 raw21180Labels = mixedMoment B raw21180step0 raw21180step0Labels := by
      have hz : ∀ j, raw21180 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21180step0 = (fun i j => raw21180 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21180step0 raw21180; decide +kernel
      have hl : raw21180step0Labels = raw21180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21180 raw21180Labels permutation434 hz
    mixedMoment B raw21180step0 raw21180step0Labels = mixedMoment B raw21180step1 raw21180step1Labels := by
      have ha : raw21180step1 = (fun i j => raw21180step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21180step1 raw21180step0; decide +kernel
      have hl : raw21180step1Labels = raw21180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21180step0 raw21180step0Labels permutation34 permutation3
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw21181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21181 raw21181Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw21181 raw21181Labels = mixedMoment B raw21181step0 raw21181step0Labels := by
      have hz : ∀ j, raw21181 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21181step0 = (fun i j => raw21181 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21181step0 raw21181; decide +kernel
      have hl : raw21181step0Labels = raw21181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21181 raw21181Labels permutation346 hz
    mixedMoment B raw21181step0 raw21181step0Labels = mixedMoment B raw21181step1 raw21181step1Labels := by
      have ha : raw21181step1 = (fun i j => raw21181step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21181step1 raw21181step0; decide +kernel
      have hl : raw21181step1Labels = raw21181step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21181step0 raw21181step0Labels permutation34 permutation3
    _ = mixedMoment B node626 node626Labels := by rfl

def raw21182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21182 raw21182Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw21182 raw21182Labels = mixedMoment B raw21182step0 raw21182step0Labels := by
      have hz : ∀ j, raw21182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21182step0 = (fun i j => raw21182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21182step0 raw21182; decide +kernel
      have hl : raw21182step0Labels = raw21182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21182 raw21182Labels permutation346 hz
    mixedMoment B raw21182step0 raw21182step0Labels = mixedMoment B raw21182step1 raw21182step1Labels := by
      have ha : raw21182step1 = (fun i j => raw21182step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21182step1 raw21182step0; decide +kernel
      have hl : raw21182step1Labels = raw21182step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21182step0 raw21182step0Labels permutation34 permutation3
    _ = mixedMoment B node1317 node1317Labels := by rfl

def raw21183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21183 raw21183Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw21183 raw21183Labels = mixedMoment B raw21183step0 raw21183step0Labels := by
      have ha : raw21183step0 = (fun i j => raw21183 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21183step0 raw21183; decide +kernel
      have hl : raw21183step0Labels = raw21183Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21183 raw21183Labels permutation178 permutation3
    _ = mixedMoment B node1327 node1327Labels := by rfl

def raw21184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21184 raw21184Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw21184 raw21184Labels = mixedMoment B raw21184step0 raw21184step0Labels := by
      have hz : ∀ j, raw21184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21184step0 = (fun i j => raw21184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21184step0 raw21184; decide +kernel
      have hl : raw21184step0Labels = raw21184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21184 raw21184Labels permutation346 hz
    mixedMoment B raw21184step0 raw21184step0Labels = mixedMoment B raw21184step1 raw21184step1Labels := by
      have ha : raw21184step1 = (fun i j => raw21184step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21184step1 raw21184step0; decide +kernel
      have hl : raw21184step1Labels = raw21184step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21184step0 raw21184step0Labels permutation34 permutation3
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw21185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21185 raw21185Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw21185 raw21185Labels = mixedMoment B raw21185step0 raw21185step0Labels := by
      have hz : ∀ j, raw21185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21185step0 = (fun i j => raw21185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21185step0 raw21185; decide +kernel
      have hl : raw21185step0Labels = raw21185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21185 raw21185Labels permutation346 hz
    mixedMoment B raw21185step0 raw21185step0Labels = mixedMoment B raw21185step1 raw21185step1Labels := by
      have ha : raw21185step1 = (fun i j => raw21185step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21185step1 raw21185step0; decide +kernel
      have hl : raw21185step1Labels = raw21185step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21185step0 raw21185step0Labels permutation34 permutation3
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw21186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21186step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw21186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21186 raw21186Labels = mixedMoment B node635 node635Labels := by
  calc
    mixedMoment B raw21186 raw21186Labels = mixedMoment B raw21186step0 raw21186step0Labels := by
      have hz : ∀ j, raw21186 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21186step0 = (fun i j => raw21186 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21186step0 raw21186; decide +kernel
      have hl : raw21186step0Labels = raw21186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21186 raw21186Labels permutation434 hz
    mixedMoment B raw21186step0 raw21186step0Labels = mixedMoment B raw21186step1 raw21186step1Labels := by
      have hz : ∀ j, raw21186step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21186step1 = (fun i j => raw21186step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21186step1 raw21186step0; decide +kernel
      have hl : raw21186step1Labels = raw21186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21186step0 raw21186step0Labels permutation80 hz
    mixedMoment B raw21186step1 raw21186step1Labels = mixedMoment B raw21186step2 raw21186step2Labels := by
      have ha : raw21186step2 = (fun i j => raw21186step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21186step2 raw21186step1; decide +kernel
      have hl : raw21186step2Labels = raw21186step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21186step1 raw21186step1Labels permutation8 permutation3
    _ = mixedMoment B node635 node635Labels := by rfl

def raw21187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21187step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21187step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw21187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21187 raw21187Labels = mixedMoment B node1324 node1324Labels := by
  calc
    mixedMoment B raw21187 raw21187Labels = mixedMoment B raw21187step0 raw21187step0Labels := by
      have hz : ∀ j, raw21187 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21187step0 = (fun i j => raw21187 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21187step0 raw21187; decide +kernel
      have hl : raw21187step0Labels = raw21187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21187 raw21187Labels permutation434 hz
    mixedMoment B raw21187step0 raw21187step0Labels = mixedMoment B raw21187step1 raw21187step1Labels := by
      have hz : ∀ j, raw21187step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21187step1 = (fun i j => raw21187step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21187step1 raw21187step0; decide +kernel
      have hl : raw21187step1Labels = raw21187step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21187step0 raw21187step0Labels permutation80 hz
    mixedMoment B raw21187step1 raw21187step1Labels = mixedMoment B raw21187step2 raw21187step2Labels := by
      have ha : raw21187step2 = (fun i j => raw21187step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21187step2 raw21187step1; decide +kernel
      have hl : raw21187step2Labels = raw21187step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21187step1 raw21187step1Labels permutation8 permutation3
    _ = mixedMoment B node1324 node1324Labels := by rfl

def raw21188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21188Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21188step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw21188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21188 raw21188Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw21188 raw21188Labels = mixedMoment B raw21188step0 raw21188step0Labels := by
      have hz : ∀ j, raw21188 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21188step0 = (fun i j => raw21188 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21188step0 raw21188; decide +kernel
      have hl : raw21188step0Labels = raw21188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21188 raw21188Labels permutation434 hz
    mixedMoment B raw21188step0 raw21188step0Labels = mixedMoment B raw21188step1 raw21188step1Labels := by
      have ha : raw21188step1 = (fun i j => raw21188step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21188step1 raw21188step0; decide +kernel
      have hl : raw21188step1Labels = raw21188step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21188step0 raw21188step0Labels permutation38 permutation3
    _ = mixedMoment B node1333 node1333Labels := by rfl

def raw21189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21189Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21189step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw21189step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21189 raw21189Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw21189 raw21189Labels = mixedMoment B raw21189step0 raw21189step0Labels := by
      have hz : ∀ j, raw21189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21189step0 = (fun i j => raw21189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21189step0 raw21189; decide +kernel
      have hl : raw21189step0Labels = raw21189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21189 raw21189Labels permutation346 hz
    mixedMoment B raw21189step0 raw21189step0Labels = mixedMoment B raw21189step1 raw21189step1Labels := by
      have ha : raw21189step1 = (fun i j => raw21189step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21189step1 raw21189step0; decide +kernel
      have hl : raw21189step1Labels = raw21189step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21189step0 raw21189step0Labels permutation38 permutation3
    _ = mixedMoment B node1333 node1333Labels := by rfl

def raw21190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw21190Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw21190step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw21190step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw21190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21190 raw21190Labels = mixedMoment B node1420 node1420Labels := by
  calc
    mixedMoment B raw21190 raw21190Labels = mixedMoment B raw21190step0 raw21190step0Labels := by
      have hz : ∀ j, raw21190 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21190step0 = (fun i j => raw21190 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21190step0 raw21190; decide +kernel
      have hl : raw21190step0Labels = raw21190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21190 raw21190Labels permutation434 hz
    mixedMoment B raw21190step0 raw21190step0Labels = mixedMoment B raw21190step1 raw21190step1Labels := by
      have hz : ∀ j, raw21190step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21190step1 = (fun i j => raw21190step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21190step1 raw21190step0; decide +kernel
      have hl : raw21190step1Labels = raw21190step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21190step0 raw21190step0Labels permutation80 hz
    mixedMoment B raw21190step1 raw21190step1Labels = mixedMoment B raw21190step2 raw21190step2Labels := by
      have ha : raw21190step2 = (fun i j => raw21190step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21190step2 raw21190step1; decide +kernel
      have hl : raw21190step2Labels = raw21190step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21190step1 raw21190step1Labels permutation8 permutation3
    _ = mixedMoment B node1420 node1420Labels := by rfl

def raw21191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21191step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21191step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21191step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21191step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw21191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21191 raw21191Labels = mixedMoment B node628 node628Labels := by
  calc
    mixedMoment B raw21191 raw21191Labels = mixedMoment B raw21191step0 raw21191step0Labels := by
      have hz : ∀ j, raw21191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21191step0 = (fun i j => raw21191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21191step0 raw21191; decide +kernel
      have hl : raw21191step0Labels = raw21191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21191 raw21191Labels permutation434 hz
    mixedMoment B raw21191step0 raw21191step0Labels = mixedMoment B raw21191step1 raw21191step1Labels := by
      have hz : ∀ j, raw21191step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21191step1 = (fun i j => raw21191step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21191step1 raw21191step0; decide +kernel
      have hl : raw21191step1Labels = raw21191step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21191step0 raw21191step0Labels permutation80 hz
    mixedMoment B raw21191step1 raw21191step1Labels = mixedMoment B raw21191step2 raw21191step2Labels := by
      have ha : raw21191step2 = (fun i j => raw21191step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21191step2 raw21191step1; decide +kernel
      have hl : raw21191step2Labels = raw21191step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21191step1 raw21191step1Labels permutation8 permutation3
    _ = mixedMoment B node628 node628Labels := by rfl

def raw21192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21192step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21192step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21192step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21192step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, -1, 2], ![-4, 3, 1]]
def raw21192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21192step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21192step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21192 raw21192Labels = mixedMoment B node936 node936Labels := by
  calc
    mixedMoment B raw21192 raw21192Labels = mixedMoment B raw21192step0 raw21192step0Labels := by
      have hz : ∀ j, raw21192 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21192step0 = (fun i j => raw21192 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21192step0 raw21192; decide +kernel
      have hl : raw21192step0Labels = raw21192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21192 raw21192Labels permutation434 hz
    mixedMoment B raw21192step0 raw21192step0Labels = mixedMoment B raw21192step1 raw21192step1Labels := by
      have hz : ∀ j, raw21192step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21192step1 = (fun i j => raw21192step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21192step1 raw21192step0; decide +kernel
      have hl : raw21192step1Labels = raw21192step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21192step0 raw21192step0Labels permutation80 hz
    mixedMoment B raw21192step1 raw21192step1Labels = mixedMoment B raw21192step2 raw21192step2Labels := by
      have ha : raw21192step2 = (fun i j => raw21192step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21192step2 raw21192step1; decide +kernel
      have hl : raw21192step2Labels = raw21192step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21192step1 raw21192step1Labels permutation31 permutation3
    mixedMoment B raw21192step2 raw21192step2Labels = mixedMoment B raw21192step3 raw21192step3Labels := by
      have ha : raw21192step3 = -raw21192step2 := by apply Matrix.ext; change ∀ i j, raw21192step3 i j = -(raw21192step2 i j); unfold raw21192step3 raw21192step2; decide +kernel
      have hl : raw21192step3Labels = raw21192step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node936 node936Labels := by rfl

def raw21193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21193Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21193step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw21193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21193 raw21193Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw21193 raw21193Labels = mixedMoment B raw21193step0 raw21193step0Labels := by
      have hz : ∀ j, raw21193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21193step0 = (fun i j => raw21193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21193step0 raw21193; decide +kernel
      have hl : raw21193step0Labels = raw21193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21193 raw21193Labels permutation434 hz
    mixedMoment B raw21193step0 raw21193step0Labels = mixedMoment B raw21193step1 raw21193step1Labels := by
      have ha : raw21193step1 = (fun i j => raw21193step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21193step1 raw21193step0; decide +kernel
      have hl : raw21193step1Labels = raw21193step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21193step0 raw21193step0Labels permutation149 permutation3
    mixedMoment B raw21193step1 raw21193step1Labels = mixedMoment B raw21193step2 raw21193step2Labels := by
      have ha : raw21193step2 = -raw21193step1 := by apply Matrix.ext; change ∀ i j, raw21193step2 i j = -(raw21193step1 i j); unfold raw21193step2 raw21193step1; decide +kernel
      have hl : raw21193step2Labels = raw21193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node911 node911Labels := by rfl

def raw21194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21194Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21194step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw21194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21194 raw21194Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw21194 raw21194Labels = mixedMoment B raw21194step0 raw21194step0Labels := by
      have hz : ∀ j, raw21194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21194step0 = (fun i j => raw21194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21194step0 raw21194; decide +kernel
      have hl : raw21194step0Labels = raw21194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21194 raw21194Labels permutation346 hz
    mixedMoment B raw21194step0 raw21194step0Labels = mixedMoment B raw21194step1 raw21194step1Labels := by
      have ha : raw21194step1 = (fun i j => raw21194step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21194step1 raw21194step0; decide +kernel
      have hl : raw21194step1Labels = raw21194step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21194step0 raw21194step0Labels permutation149 permutation3
    mixedMoment B raw21194step1 raw21194step1Labels = mixedMoment B raw21194step2 raw21194step2Labels := by
      have ha : raw21194step2 = -raw21194step1 := by apply Matrix.ext; change ∀ i j, raw21194step2 i j = -(raw21194step1 i j); unfold raw21194step2 raw21194step1; decide +kernel
      have hl : raw21194step2Labels = raw21194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node911 node911Labels := by rfl

def raw21195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw21195Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw21195step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw21195step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw21195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21195step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw21195step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21195 raw21195Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw21195 raw21195Labels = mixedMoment B raw21195step0 raw21195step0Labels := by
      have hz : ∀ j, raw21195 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21195step0 = (fun i j => raw21195 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21195step0 raw21195; decide +kernel
      have hl : raw21195step0Labels = raw21195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21195 raw21195Labels permutation434 hz
    mixedMoment B raw21195step0 raw21195step0Labels = mixedMoment B raw21195step1 raw21195step1Labels := by
      have hz : ∀ j, raw21195step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21195step1 = (fun i j => raw21195step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21195step1 raw21195step0; decide +kernel
      have hl : raw21195step1Labels = raw21195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21195step0 raw21195step0Labels permutation80 hz
    mixedMoment B raw21195step1 raw21195step1Labels = mixedMoment B raw21195step2 raw21195step2Labels := by
      have ha : raw21195step2 = (fun i j => raw21195step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21195step2 raw21195step1; decide +kernel
      have hl : raw21195step2Labels = raw21195step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21195step1 raw21195step1Labels permutation29 permutation3
    mixedMoment B raw21195step2 raw21195step2Labels = mixedMoment B raw21195step3 raw21195step3Labels := by
      have ha : raw21195step3 = -raw21195step2 := by apply Matrix.ext; change ∀ i j, raw21195step3 i j = -(raw21195step2 i j); unfold raw21195step3 raw21195step2; decide +kernel
      have hl : raw21195step3Labels = raw21195step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1027 node1027Labels := by rfl

def raw21196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21196step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21196step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw21196step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21196step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw21196step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21196step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw21196step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21196 raw21196Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw21196 raw21196Labels = mixedMoment B raw21196step0 raw21196step0Labels := by
      have hz : ∀ j, raw21196 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21196step0 = (fun i j => raw21196 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21196step0 raw21196; decide +kernel
      have hl : raw21196step0Labels = raw21196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21196 raw21196Labels permutation434 hz
    mixedMoment B raw21196step0 raw21196step0Labels = mixedMoment B raw21196step1 raw21196step1Labels := by
      have hz : ∀ j, raw21196step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21196step1 = (fun i j => raw21196step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21196step1 raw21196step0; decide +kernel
      have hl : raw21196step1Labels = raw21196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21196step0 raw21196step0Labels permutation80 hz
    mixedMoment B raw21196step1 raw21196step1Labels = mixedMoment B raw21196step2 raw21196step2Labels := by
      have ha : raw21196step2 = (fun i j => raw21196step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21196step2 raw21196step1; decide +kernel
      have hl : raw21196step2Labels = raw21196step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21196step1 raw21196step1Labels permutation8 permutation7
    mixedMoment B raw21196step2 raw21196step2Labels = mixedMoment B raw21196step3 raw21196step3Labels := by
      have ha : raw21196step3 = -raw21196step2 := by apply Matrix.ext; change ∀ i j, raw21196step3 i j = -(raw21196step2 i j); unfold raw21196step3 raw21196step2; decide +kernel
      have hl : raw21196step3Labels = raw21196step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21196step3 raw21196step3Labels = mixedMoment B raw21196step4 raw21196step4Labels := by
      have ha : raw21196step4 = raw21196step3 := by apply Matrix.ext; unfold raw21196step4 raw21196step3; decide +kernel
      have hl : raw21196step3Labels = labelEmbedding1 ∘ raw21196step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21196step3 raw21196step3Labels raw21196step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw21197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21197step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21197step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw21197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21197step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw21197step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21197step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw21197step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21197 raw21197Labels = mixedMoment B node1535 node1535Labels := by
  calc
    mixedMoment B raw21197 raw21197Labels = mixedMoment B raw21197step0 raw21197step0Labels := by
      have hz : ∀ j, raw21197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21197step0 = (fun i j => raw21197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21197step0 raw21197; decide +kernel
      have hl : raw21197step0Labels = raw21197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21197 raw21197Labels permutation434 hz
    mixedMoment B raw21197step0 raw21197step0Labels = mixedMoment B raw21197step1 raw21197step1Labels := by
      have hz : ∀ j, raw21197step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21197step1 = (fun i j => raw21197step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21197step1 raw21197step0; decide +kernel
      have hl : raw21197step1Labels = raw21197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21197step0 raw21197step0Labels permutation80 hz
    mixedMoment B raw21197step1 raw21197step1Labels = mixedMoment B raw21197step2 raw21197step2Labels := by
      have ha : raw21197step2 = (fun i j => raw21197step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21197step2 raw21197step1; decide +kernel
      have hl : raw21197step2Labels = raw21197step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21197step1 raw21197step1Labels permutation8 permutation7
    mixedMoment B raw21197step2 raw21197step2Labels = mixedMoment B raw21197step3 raw21197step3Labels := by
      have ha : raw21197step3 = -raw21197step2 := by apply Matrix.ext; change ∀ i j, raw21197step3 i j = -(raw21197step2 i j); unfold raw21197step3 raw21197step2; decide +kernel
      have hl : raw21197step3Labels = raw21197step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21197step3 raw21197step3Labels = mixedMoment B raw21197step4 raw21197step4Labels := by
      have ha : raw21197step4 = raw21197step3 := by apply Matrix.ext; unfold raw21197step4 raw21197step3; decide +kernel
      have hl : raw21197step3Labels = labelEmbedding1 ∘ raw21197step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21197step3 raw21197step3Labels raw21197step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1535 node1535Labels := by rfl

def raw21198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw21198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw21198step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw21198step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21198 raw21198Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw21198 raw21198Labels = mixedMoment B raw21198step0 raw21198step0Labels := by
      have hz : ∀ j, raw21198 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21198step0 = (fun i j => raw21198 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21198step0 raw21198; decide +kernel
      have hl : raw21198step0Labels = raw21198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21198 raw21198Labels permutation434 hz
    mixedMoment B raw21198step0 raw21198step0Labels = mixedMoment B raw21198step1 raw21198step1Labels := by
      have ha : raw21198step1 = (fun i j => raw21198step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21198step1 raw21198step0; decide +kernel
      have hl : raw21198step1Labels = raw21198step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21198step0 raw21198step0Labels permutation38 permutation7
    mixedMoment B raw21198step1 raw21198step1Labels = mixedMoment B raw21198step2 raw21198step2Labels := by
      have ha : raw21198step2 = -raw21198step1 := by apply Matrix.ext; change ∀ i j, raw21198step2 i j = -(raw21198step1 i j); unfold raw21198step2 raw21198step1; decide +kernel
      have hl : raw21198step2Labels = raw21198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21198step2 raw21198step2Labels = mixedMoment B raw21198step3 raw21198step3Labels := by
      have ha : raw21198step3 = raw21198step2 := by apply Matrix.ext; unfold raw21198step3 raw21198step2; decide +kernel
      have hl : raw21198step2Labels = labelEmbedding1 ∘ raw21198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21198step2 raw21198step2Labels raw21198step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1690 node1690Labels := by rfl

def raw21199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw21199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw21199step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21199step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw21199step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21199 raw21199Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw21199 raw21199Labels = mixedMoment B raw21199step0 raw21199step0Labels := by
      have hz : ∀ j, raw21199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21199step0 = (fun i j => raw21199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21199step0 raw21199; decide +kernel
      have hl : raw21199step0Labels = raw21199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21199 raw21199Labels permutation346 hz
    mixedMoment B raw21199step0 raw21199step0Labels = mixedMoment B raw21199step1 raw21199step1Labels := by
      have ha : raw21199step1 = (fun i j => raw21199step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21199step1 raw21199step0; decide +kernel
      have hl : raw21199step1Labels = raw21199step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21199step0 raw21199step0Labels permutation38 permutation7
    mixedMoment B raw21199step1 raw21199step1Labels = mixedMoment B raw21199step2 raw21199step2Labels := by
      have ha : raw21199step2 = -raw21199step1 := by apply Matrix.ext; change ∀ i j, raw21199step2 i j = -(raw21199step1 i j); unfold raw21199step2 raw21199step1; decide +kernel
      have hl : raw21199step2Labels = raw21199step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21199step2 raw21199step2Labels = mixedMoment B raw21199step3 raw21199step3Labels := by
      have ha : raw21199step3 = raw21199step2 := by apply Matrix.ext; unfold raw21199step3 raw21199step2; decide +kernel
      have hl : raw21199step2Labels = labelEmbedding1 ∘ raw21199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21199step2 raw21199step2Labels raw21199step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1690 node1690Labels := by rfl

def raw21200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw21200step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21200step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21200step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21200step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21200 raw21200Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw21200 raw21200Labels = mixedMoment B raw21200step0 raw21200step0Labels := by
      have hz : ∀ j, raw21200 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21200step0 = (fun i j => raw21200 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21200step0 raw21200; decide +kernel
      have hl : raw21200step0Labels = raw21200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21200 raw21200Labels permutation434 hz
    mixedMoment B raw21200step0 raw21200step0Labels = mixedMoment B raw21200step1 raw21200step1Labels := by
      have hz : ∀ j, raw21200step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21200step1 = (fun i j => raw21200step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21200step1 raw21200step0; decide +kernel
      have hl : raw21200step1Labels = raw21200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21200step0 raw21200step0Labels permutation80 hz
    mixedMoment B raw21200step1 raw21200step1Labels = mixedMoment B raw21200step2 raw21200step2Labels := by
      have ha : raw21200step2 = (fun i j => raw21200step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21200step2 raw21200step1; decide +kernel
      have hl : raw21200step2Labels = raw21200step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21200step1 raw21200step1Labels permutation10 permutation7
    mixedMoment B raw21200step2 raw21200step2Labels = mixedMoment B raw21200step3 raw21200step3Labels := by
      have ha : raw21200step3 = -raw21200step2 := by apply Matrix.ext; change ∀ i j, raw21200step3 i j = -(raw21200step2 i j); unfold raw21200step3 raw21200step2; decide +kernel
      have hl : raw21200step3Labels = raw21200step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21200step3 raw21200step3Labels = mixedMoment B raw21200step4 raw21200step4Labels := by
      have ha : raw21200step4 = raw21200step3 := by apply Matrix.ext; unfold raw21200step4 raw21200step3; decide +kernel
      have hl : raw21200step3Labels = labelEmbedding1 ∘ raw21200step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21200step3 raw21200step3Labels raw21200step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw21201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21201step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21201step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21201 raw21201Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw21201 raw21201Labels = mixedMoment B raw21201step0 raw21201step0Labels := by
      have hz : ∀ j, raw21201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21201step0 = (fun i j => raw21201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21201step0 raw21201; decide +kernel
      have hl : raw21201step0Labels = raw21201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21201 raw21201Labels permutation434 hz
    mixedMoment B raw21201step0 raw21201step0Labels = mixedMoment B raw21201step1 raw21201step1Labels := by
      have ha : raw21201step1 = (fun i j => raw21201step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21201step1 raw21201step0; decide +kernel
      have hl : raw21201step1Labels = raw21201step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21201step0 raw21201step0Labels permutation38 permutation7
    mixedMoment B raw21201step1 raw21201step1Labels = mixedMoment B raw21201step2 raw21201step2Labels := by
      have ha : raw21201step2 = -raw21201step1 := by apply Matrix.ext; change ∀ i j, raw21201step2 i j = -(raw21201step1 i j); unfold raw21201step2 raw21201step1; decide +kernel
      have hl : raw21201step2Labels = raw21201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21201step2 raw21201step2Labels = mixedMoment B raw21201step3 raw21201step3Labels := by
      have ha : raw21201step3 = raw21201step2 := by apply Matrix.ext; unfold raw21201step3 raw21201step2; decide +kernel
      have hl : raw21201step2Labels = labelEmbedding1 ∘ raw21201step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21201step2 raw21201step2Labels raw21201step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

def raw21202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw21202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw21202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw21202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21202 raw21202Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw21202 raw21202Labels = mixedMoment B raw21202step0 raw21202step0Labels := by
      have hz : ∀ j, raw21202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21202step0 = (fun i j => raw21202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21202step0 raw21202; decide +kernel
      have hl : raw21202step0Labels = raw21202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21202 raw21202Labels permutation434 hz
    mixedMoment B raw21202step0 raw21202step0Labels = mixedMoment B raw21202step1 raw21202step1Labels := by
      have ha : raw21202step1 = (fun i j => raw21202step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21202step1 raw21202step0; decide +kernel
      have hl : raw21202step1Labels = raw21202step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21202step0 raw21202step0Labels permutation38 permutation7
    mixedMoment B raw21202step1 raw21202step1Labels = mixedMoment B raw21202step2 raw21202step2Labels := by
      have ha : raw21202step2 = -raw21202step1 := by apply Matrix.ext; change ∀ i j, raw21202step2 i j = -(raw21202step1 i j); unfold raw21202step2 raw21202step1; decide +kernel
      have hl : raw21202step2Labels = raw21202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21202step2 raw21202step2Labels = mixedMoment B raw21202step3 raw21202step3Labels := by
      have ha : raw21202step3 = raw21202step2 := by apply Matrix.ext; unfold raw21202step3 raw21202step2; decide +kernel
      have hl : raw21202step2Labels = labelEmbedding1 ∘ raw21202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21202step2 raw21202step2Labels raw21202step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

def raw21203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21203step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21203step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21203step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21203step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21203 raw21203Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw21203 raw21203Labels = mixedMoment B raw21203step0 raw21203step0Labels := by
      have ha : raw21203step0 = (fun i j => raw21203 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21203step0 raw21203; decide +kernel
      have hl : raw21203step0Labels = raw21203Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21203 raw21203Labels permutation206 permutation7
    mixedMoment B raw21203step0 raw21203step0Labels = mixedMoment B raw21203step1 raw21203step1Labels := by
      have ha : raw21203step1 = -raw21203step0 := by apply Matrix.ext; change ∀ i j, raw21203step1 i j = -(raw21203step0 i j); unfold raw21203step1 raw21203step0; decide +kernel
      have hl : raw21203step1Labels = raw21203step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21203step1 raw21203step1Labels = mixedMoment B raw21203step2 raw21203step2Labels := by
      have ha : raw21203step2 = raw21203step1 := by apply Matrix.ext; unfold raw21203step2 raw21203step1; decide +kernel
      have hl : raw21203step1Labels = labelEmbedding1 ∘ raw21203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21203step1 raw21203step1Labels raw21203step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

def raw21204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw21204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw21204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21204step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw21204step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21204 raw21204Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw21204 raw21204Labels = mixedMoment B raw21204step0 raw21204step0Labels := by
      have hz : ∀ j, raw21204 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21204step0 = (fun i j => raw21204 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21204step0 raw21204; decide +kernel
      have hl : raw21204step0Labels = raw21204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21204 raw21204Labels permutation434 hz
    mixedMoment B raw21204step0 raw21204step0Labels = mixedMoment B raw21204step1 raw21204step1Labels := by
      have ha : raw21204step1 = (fun i j => raw21204step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21204step1 raw21204step0; decide +kernel
      have hl : raw21204step1Labels = raw21204step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21204step0 raw21204step0Labels permutation38 permutation7
    mixedMoment B raw21204step1 raw21204step1Labels = mixedMoment B raw21204step2 raw21204step2Labels := by
      have ha : raw21204step2 = -raw21204step1 := by apply Matrix.ext; change ∀ i j, raw21204step2 i j = -(raw21204step1 i j); unfold raw21204step2 raw21204step1; decide +kernel
      have hl : raw21204step2Labels = raw21204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21204step2 raw21204step2Labels = mixedMoment B raw21204step3 raw21204step3Labels := by
      have ha : raw21204step3 = raw21204step2 := by apply Matrix.ext; unfold raw21204step3 raw21204step2; decide +kernel
      have hl : raw21204step2Labels = labelEmbedding1 ∘ raw21204step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21204step2 raw21204step2Labels raw21204step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

def raw21205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21205step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21205step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21205step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21205step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21205step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21205 raw21205Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw21205 raw21205Labels = mixedMoment B raw21205step0 raw21205step0Labels := by
      have hz : ∀ j, raw21205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21205step0 = (fun i j => raw21205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21205step0 raw21205; decide +kernel
      have hl : raw21205step0Labels = raw21205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21205 raw21205Labels permutation346 hz
    mixedMoment B raw21205step0 raw21205step0Labels = mixedMoment B raw21205step1 raw21205step1Labels := by
      have ha : raw21205step1 = (fun i j => raw21205step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21205step1 raw21205step0; decide +kernel
      have hl : raw21205step1Labels = raw21205step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21205step0 raw21205step0Labels permutation38 permutation7
    mixedMoment B raw21205step1 raw21205step1Labels = mixedMoment B raw21205step2 raw21205step2Labels := by
      have ha : raw21205step2 = -raw21205step1 := by apply Matrix.ext; change ∀ i j, raw21205step2 i j = -(raw21205step1 i j); unfold raw21205step2 raw21205step1; decide +kernel
      have hl : raw21205step2Labels = raw21205step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21205step2 raw21205step2Labels = mixedMoment B raw21205step3 raw21205step3Labels := by
      have ha : raw21205step3 = raw21205step2 := by apply Matrix.ext; unfold raw21205step3 raw21205step2; decide +kernel
      have hl : raw21205step2Labels = labelEmbedding1 ∘ raw21205step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21205step2 raw21205step2Labels raw21205step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

def raw21206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw21206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw21206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw21206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21206 raw21206Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw21206 raw21206Labels = mixedMoment B raw21206step0 raw21206step0Labels := by
      have hz : ∀ j, raw21206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21206step0 = (fun i j => raw21206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21206step0 raw21206; decide +kernel
      have hl : raw21206step0Labels = raw21206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21206 raw21206Labels permutation346 hz
    mixedMoment B raw21206step0 raw21206step0Labels = mixedMoment B raw21206step1 raw21206step1Labels := by
      have ha : raw21206step1 = (fun i j => raw21206step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21206step1 raw21206step0; decide +kernel
      have hl : raw21206step1Labels = raw21206step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21206step0 raw21206step0Labels permutation38 permutation7
    mixedMoment B raw21206step1 raw21206step1Labels = mixedMoment B raw21206step2 raw21206step2Labels := by
      have ha : raw21206step2 = -raw21206step1 := by apply Matrix.ext; change ∀ i j, raw21206step2 i j = -(raw21206step1 i j); unfold raw21206step2 raw21206step1; decide +kernel
      have hl : raw21206step2Labels = raw21206step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21206step2 raw21206step2Labels = mixedMoment B raw21206step3 raw21206step3Labels := by
      have ha : raw21206step3 = raw21206step2 := by apply Matrix.ext; unfold raw21206step3 raw21206step2; decide +kernel
      have hl : raw21206step2Labels = labelEmbedding1 ∘ raw21206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21206step2 raw21206step2Labels raw21206step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

def raw21207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21207step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21207step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21207 raw21207Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw21207 raw21207Labels = mixedMoment B raw21207step0 raw21207step0Labels := by
      have ha : raw21207step0 = (fun i j => raw21207 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21207step0 raw21207; decide +kernel
      have hl : raw21207step0Labels = raw21207Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21207 raw21207Labels permutation182 permutation7
    mixedMoment B raw21207step0 raw21207step0Labels = mixedMoment B raw21207step1 raw21207step1Labels := by
      have ha : raw21207step1 = -raw21207step0 := by apply Matrix.ext; change ∀ i j, raw21207step1 i j = -(raw21207step0 i j); unfold raw21207step1 raw21207step0; decide +kernel
      have hl : raw21207step1Labels = raw21207step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21207step1 raw21207step1Labels = mixedMoment B raw21207step2 raw21207step2Labels := by
      have ha : raw21207step2 = raw21207step1 := by apply Matrix.ext; unfold raw21207step2 raw21207step1; decide +kernel
      have hl : raw21207step1Labels = labelEmbedding1 ∘ raw21207step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21207step1 raw21207step1Labels raw21207step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

def raw21208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw21208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw21208step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw21208step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21208 raw21208Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw21208 raw21208Labels = mixedMoment B raw21208step0 raw21208step0Labels := by
      have hz : ∀ j, raw21208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21208step0 = (fun i j => raw21208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21208step0 raw21208; decide +kernel
      have hl : raw21208step0Labels = raw21208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21208 raw21208Labels permutation346 hz
    mixedMoment B raw21208step0 raw21208step0Labels = mixedMoment B raw21208step1 raw21208step1Labels := by
      have ha : raw21208step1 = (fun i j => raw21208step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21208step1 raw21208step0; decide +kernel
      have hl : raw21208step1Labels = raw21208step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21208step0 raw21208step0Labels permutation38 permutation7
    mixedMoment B raw21208step1 raw21208step1Labels = mixedMoment B raw21208step2 raw21208step2Labels := by
      have ha : raw21208step2 = -raw21208step1 := by apply Matrix.ext; change ∀ i j, raw21208step2 i j = -(raw21208step1 i j); unfold raw21208step2 raw21208step1; decide +kernel
      have hl : raw21208step2Labels = raw21208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21208step2 raw21208step2Labels = mixedMoment B raw21208step3 raw21208step3Labels := by
      have ha : raw21208step3 = raw21208step2 := by apply Matrix.ext; unfold raw21208step3 raw21208step2; decide +kernel
      have hl : raw21208step2Labels = labelEmbedding1 ∘ raw21208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21208step2 raw21208step2Labels raw21208step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

def raw21209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21209step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21209step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21209step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw21209step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21209step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw21209step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21209step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw21209step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21209 raw21209Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw21209 raw21209Labels = mixedMoment B raw21209step0 raw21209step0Labels := by
      have hz : ∀ j, raw21209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21209step0 = (fun i j => raw21209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21209step0 raw21209; decide +kernel
      have hl : raw21209step0Labels = raw21209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21209 raw21209Labels permutation434 hz
    mixedMoment B raw21209step0 raw21209step0Labels = mixedMoment B raw21209step1 raw21209step1Labels := by
      have hz : ∀ j, raw21209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21209step1 = (fun i j => raw21209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21209step1 raw21209step0; decide +kernel
      have hl : raw21209step1Labels = raw21209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21209step0 raw21209step0Labels permutation80 hz
    mixedMoment B raw21209step1 raw21209step1Labels = mixedMoment B raw21209step2 raw21209step2Labels := by
      have ha : raw21209step2 = (fun i j => raw21209step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21209step2 raw21209step1; decide +kernel
      have hl : raw21209step2Labels = raw21209step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21209step1 raw21209step1Labels permutation8 permutation7
    mixedMoment B raw21209step2 raw21209step2Labels = mixedMoment B raw21209step3 raw21209step3Labels := by
      have ha : raw21209step3 = -raw21209step2 := by apply Matrix.ext; change ∀ i j, raw21209step3 i j = -(raw21209step2 i j); unfold raw21209step3 raw21209step2; decide +kernel
      have hl : raw21209step3Labels = raw21209step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21209step3 raw21209step3Labels = mixedMoment B raw21209step4 raw21209step4Labels := by
      have ha : raw21209step4 = raw21209step3 := by apply Matrix.ext; unfold raw21209step4 raw21209step3; decide +kernel
      have hl : raw21209step3Labels = labelEmbedding1 ∘ raw21209step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21209step3 raw21209step3Labels raw21209step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

def raw21210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21210step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw21210step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21210step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw21210step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21210step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw21210step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21210 raw21210Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw21210 raw21210Labels = mixedMoment B raw21210step0 raw21210step0Labels := by
      have hz : ∀ j, raw21210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21210step0 = (fun i j => raw21210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21210step0 raw21210; decide +kernel
      have hl : raw21210step0Labels = raw21210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21210 raw21210Labels permutation434 hz
    mixedMoment B raw21210step0 raw21210step0Labels = mixedMoment B raw21210step1 raw21210step1Labels := by
      have hz : ∀ j, raw21210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21210step1 = (fun i j => raw21210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21210step1 raw21210step0; decide +kernel
      have hl : raw21210step1Labels = raw21210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21210step0 raw21210step0Labels permutation80 hz
    mixedMoment B raw21210step1 raw21210step1Labels = mixedMoment B raw21210step2 raw21210step2Labels := by
      have ha : raw21210step2 = (fun i j => raw21210step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21210step2 raw21210step1; decide +kernel
      have hl : raw21210step2Labels = raw21210step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21210step1 raw21210step1Labels permutation8 permutation7
    mixedMoment B raw21210step2 raw21210step2Labels = mixedMoment B raw21210step3 raw21210step3Labels := by
      have ha : raw21210step3 = -raw21210step2 := by apply Matrix.ext; change ∀ i j, raw21210step3 i j = -(raw21210step2 i j); unfold raw21210step3 raw21210step2; decide +kernel
      have hl : raw21210step3Labels = raw21210step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21210step3 raw21210step3Labels = mixedMoment B raw21210step4 raw21210step4Labels := by
      have ha : raw21210step4 = raw21210step3 := by apply Matrix.ext; unfold raw21210step4 raw21210step3; decide +kernel
      have hl : raw21210step3Labels = labelEmbedding1 ∘ raw21210step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21210step3 raw21210step3Labels raw21210step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

def raw21211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw21211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw21211step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21211step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw21211step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21211 raw21211Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw21211 raw21211Labels = mixedMoment B raw21211step0 raw21211step0Labels := by
      have hz : ∀ j, raw21211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21211step0 = (fun i j => raw21211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21211step0 raw21211; decide +kernel
      have hl : raw21211step0Labels = raw21211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21211 raw21211Labels permutation434 hz
    mixedMoment B raw21211step0 raw21211step0Labels = mixedMoment B raw21211step1 raw21211step1Labels := by
      have ha : raw21211step1 = (fun i j => raw21211step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21211step1 raw21211step0; decide +kernel
      have hl : raw21211step1Labels = raw21211step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21211step0 raw21211step0Labels permutation38 permutation7
    mixedMoment B raw21211step1 raw21211step1Labels = mixedMoment B raw21211step2 raw21211step2Labels := by
      have ha : raw21211step2 = -raw21211step1 := by apply Matrix.ext; change ∀ i j, raw21211step2 i j = -(raw21211step1 i j); unfold raw21211step2 raw21211step1; decide +kernel
      have hl : raw21211step2Labels = raw21211step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21211step2 raw21211step2Labels = mixedMoment B raw21211step3 raw21211step3Labels := by
      have ha : raw21211step3 = raw21211step2 := by apply Matrix.ext; unfold raw21211step3 raw21211step2; decide +kernel
      have hl : raw21211step2Labels = labelEmbedding1 ∘ raw21211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21211step2 raw21211step2Labels raw21211step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw21212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21212step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw21212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw21212step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21212step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw21212step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21212 raw21212Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw21212 raw21212Labels = mixedMoment B raw21212step0 raw21212step0Labels := by
      have hz : ∀ j, raw21212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21212step0 = (fun i j => raw21212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21212step0 raw21212; decide +kernel
      have hl : raw21212step0Labels = raw21212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21212 raw21212Labels permutation346 hz
    mixedMoment B raw21212step0 raw21212step0Labels = mixedMoment B raw21212step1 raw21212step1Labels := by
      have ha : raw21212step1 = (fun i j => raw21212step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21212step1 raw21212step0; decide +kernel
      have hl : raw21212step1Labels = raw21212step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21212step0 raw21212step0Labels permutation38 permutation7
    mixedMoment B raw21212step1 raw21212step1Labels = mixedMoment B raw21212step2 raw21212step2Labels := by
      have ha : raw21212step2 = -raw21212step1 := by apply Matrix.ext; change ∀ i j, raw21212step2 i j = -(raw21212step1 i j); unfold raw21212step2 raw21212step1; decide +kernel
      have hl : raw21212step2Labels = raw21212step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21212step2 raw21212step2Labels = mixedMoment B raw21212step3 raw21212step3Labels := by
      have ha : raw21212step3 = raw21212step2 := by apply Matrix.ext; unfold raw21212step3 raw21212step2; decide +kernel
      have hl : raw21212step2Labels = labelEmbedding1 ∘ raw21212step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21212step2 raw21212step2Labels raw21212step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw21213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21213step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21213step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw21213step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw21213step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21213step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw21213step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21213 raw21213Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw21213 raw21213Labels = mixedMoment B raw21213step0 raw21213step0Labels := by
      have hz : ∀ j, raw21213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21213step0 = (fun i j => raw21213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21213step0 raw21213; decide +kernel
      have hl : raw21213step0Labels = raw21213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21213 raw21213Labels permutation434 hz
    mixedMoment B raw21213step0 raw21213step0Labels = mixedMoment B raw21213step1 raw21213step1Labels := by
      have hz : ∀ j, raw21213step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21213step1 = (fun i j => raw21213step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21213step1 raw21213step0; decide +kernel
      have hl : raw21213step1Labels = raw21213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21213step0 raw21213step0Labels permutation80 hz
    mixedMoment B raw21213step1 raw21213step1Labels = mixedMoment B raw21213step2 raw21213step2Labels := by
      have ha : raw21213step2 = (fun i j => raw21213step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21213step2 raw21213step1; decide +kernel
      have hl : raw21213step2Labels = raw21213step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21213step1 raw21213step1Labels permutation8 permutation7
    mixedMoment B raw21213step2 raw21213step2Labels = mixedMoment B raw21213step3 raw21213step3Labels := by
      have ha : raw21213step3 = -raw21213step2 := by apply Matrix.ext; change ∀ i j, raw21213step3 i j = -(raw21213step2 i j); unfold raw21213step3 raw21213step2; decide +kernel
      have hl : raw21213step3Labels = raw21213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21213step3 raw21213step3Labels = mixedMoment B raw21213step4 raw21213step4Labels := by
      have ha : raw21213step4 = raw21213step3 := by apply Matrix.ext; unfold raw21213step4 raw21213step3; decide +kernel
      have hl : raw21213step3Labels = labelEmbedding1 ∘ raw21213step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21213step3 raw21213step3Labels raw21213step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

def raw21214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21214step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21214step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21214step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21214step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21214step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21214step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21214 raw21214Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw21214 raw21214Labels = mixedMoment B raw21214step0 raw21214step0Labels := by
      have hz : ∀ j, raw21214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21214step0 = (fun i j => raw21214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21214step0 raw21214; decide +kernel
      have hl : raw21214step0Labels = raw21214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21214 raw21214Labels permutation434 hz
    mixedMoment B raw21214step0 raw21214step0Labels = mixedMoment B raw21214step1 raw21214step1Labels := by
      have hz : ∀ j, raw21214step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21214step1 = (fun i j => raw21214step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21214step1 raw21214step0; decide +kernel
      have hl : raw21214step1Labels = raw21214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21214step0 raw21214step0Labels permutation80 hz
    mixedMoment B raw21214step1 raw21214step1Labels = mixedMoment B raw21214step2 raw21214step2Labels := by
      have ha : raw21214step2 = (fun i j => raw21214step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw21214step2 raw21214step1; decide +kernel
      have hl : raw21214step2Labels = raw21214step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21214step1 raw21214step1Labels permutation30 permutation5
    mixedMoment B raw21214step2 raw21214step2Labels = mixedMoment B raw21214step3 raw21214step3Labels := by
      have ha : raw21214step3 = raw21214step2 := by apply Matrix.ext; unfold raw21214step3 raw21214step2; decide +kernel
      have hl : raw21214step2Labels = labelEmbedding1 ∘ raw21214step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21214step2 raw21214step2Labels raw21214step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

def raw21215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw21215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw21215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21215 raw21215Labels = mixedMoment B node1688 node1688Labels := by
  calc
    mixedMoment B raw21215 raw21215Labels = mixedMoment B raw21215step0 raw21215step0Labels := by
      have hz : ∀ j, raw21215 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21215step0 = (fun i j => raw21215 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21215step0 raw21215; decide +kernel
      have hl : raw21215step0Labels = raw21215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21215 raw21215Labels permutation434 hz
    mixedMoment B raw21215step0 raw21215step0Labels = mixedMoment B raw21215step1 raw21215step1Labels := by
      have ha : raw21215step1 = (fun i j => raw21215step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw21215step1 raw21215step0; decide +kernel
      have hl : raw21215step1Labels = raw21215step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21215step0 raw21215step0Labels permutation149 permutation5
    mixedMoment B raw21215step1 raw21215step1Labels = mixedMoment B raw21215step2 raw21215step2Labels := by
      have ha : raw21215step2 = raw21215step1 := by apply Matrix.ext; unfold raw21215step2 raw21215step1; decide +kernel
      have hl : raw21215step1Labels = labelEmbedding1 ∘ raw21215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21215step1 raw21215step1Labels raw21215step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1688 node1688Labels := by rfl

def raw21216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21216step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw21216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw21216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21216 raw21216Labels = mixedMoment B node1688 node1688Labels := by
  calc
    mixedMoment B raw21216 raw21216Labels = mixedMoment B raw21216step0 raw21216step0Labels := by
      have hz : ∀ j, raw21216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21216step0 = (fun i j => raw21216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21216step0 raw21216; decide +kernel
      have hl : raw21216step0Labels = raw21216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21216 raw21216Labels permutation346 hz
    mixedMoment B raw21216step0 raw21216step0Labels = mixedMoment B raw21216step1 raw21216step1Labels := by
      have ha : raw21216step1 = (fun i j => raw21216step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw21216step1 raw21216step0; decide +kernel
      have hl : raw21216step1Labels = raw21216step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21216step0 raw21216step0Labels permutation149 permutation5
    mixedMoment B raw21216step1 raw21216step1Labels = mixedMoment B raw21216step2 raw21216step2Labels := by
      have ha : raw21216step2 = raw21216step1 := by apply Matrix.ext; unfold raw21216step2 raw21216step1; decide +kernel
      have hl : raw21216step1Labels = labelEmbedding1 ∘ raw21216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21216step1 raw21216step1Labels raw21216step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1688 node1688Labels := by rfl

def raw21217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw21217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw21217step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw21217step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21217step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw21217step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21217step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw21217step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21217 raw21217Labels = mixedMoment B node1749 node1749Labels := by
  calc
    mixedMoment B raw21217 raw21217Labels = mixedMoment B raw21217step0 raw21217step0Labels := by
      have hz : ∀ j, raw21217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21217step0 = (fun i j => raw21217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21217step0 raw21217; decide +kernel
      have hl : raw21217step0Labels = raw21217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21217 raw21217Labels permutation434 hz
    mixedMoment B raw21217step0 raw21217step0Labels = mixedMoment B raw21217step1 raw21217step1Labels := by
      have hz : ∀ j, raw21217step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21217step1 = (fun i j => raw21217step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21217step1 raw21217step0; decide +kernel
      have hl : raw21217step1Labels = raw21217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21217step0 raw21217step0Labels permutation80 hz
    mixedMoment B raw21217step1 raw21217step1Labels = mixedMoment B raw21217step2 raw21217step2Labels := by
      have ha : raw21217step2 = (fun i j => raw21217step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw21217step2 raw21217step1; decide +kernel
      have hl : raw21217step2Labels = raw21217step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21217step1 raw21217step1Labels permutation29 permutation5
    mixedMoment B raw21217step2 raw21217step2Labels = mixedMoment B raw21217step3 raw21217step3Labels := by
      have ha : raw21217step3 = raw21217step2 := by apply Matrix.ext; unfold raw21217step3 raw21217step2; decide +kernel
      have hl : raw21217step2Labels = labelEmbedding1 ∘ raw21217step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21217step2 raw21217step2Labels raw21217step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1749 node1749Labels := by rfl

def raw21218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21218step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21218 raw21218Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw21218 raw21218Labels = mixedMoment B raw21218step0 raw21218step0Labels := by
      have hz : ∀ j, raw21218 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21218step0 = (fun i j => raw21218 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21218step0 raw21218; decide +kernel
      have hl : raw21218step0Labels = raw21218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21218 raw21218Labels permutation434 hz
    mixedMoment B raw21218step0 raw21218step0Labels = mixedMoment B raw21218step1 raw21218step1Labels := by
      have hz : ∀ j, raw21218step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21218step1 = (fun i j => raw21218step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21218step1 raw21218step0; decide +kernel
      have hl : raw21218step1Labels = raw21218step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21218step0 raw21218step0Labels permutation80 hz
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw21219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21219 raw21219Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw21219 raw21219Labels = mixedMoment B raw21219step0 raw21219step0Labels := by
      have hz : ∀ j, raw21219 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21219step0 = (fun i j => raw21219 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21219step0 raw21219; decide +kernel
      have hl : raw21219step0Labels = raw21219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21219 raw21219Labels permutation434 hz
    mixedMoment B raw21219step0 raw21219step0Labels = mixedMoment B raw21219step1 raw21219step1Labels := by
      have hz : ∀ j, raw21219step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21219step1 = (fun i j => raw21219step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21219step1 raw21219step0; decide +kernel
      have hl : raw21219step1Labels = raw21219step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21219step0 raw21219step0Labels permutation80 hz
    _ = mixedMoment B node611 node611Labels := by rfl

def raw21220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21220 raw21220Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw21220 raw21220Labels = mixedMoment B raw21220step0 raw21220step0Labels := by
      have hz : ∀ j, raw21220 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21220step0 = (fun i j => raw21220 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21220step0 raw21220; decide +kernel
      have hl : raw21220step0Labels = raw21220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21220 raw21220Labels permutation434 hz
    _ = mixedMoment B node581 node581Labels := by rfl

def raw21221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21221 raw21221Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw21221 raw21221Labels = mixedMoment B raw21221step0 raw21221step0Labels := by
      have hz : ∀ j, raw21221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21221step0 = (fun i j => raw21221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21221step0 raw21221; decide +kernel
      have hl : raw21221step0Labels = raw21221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21221 raw21221Labels permutation346 hz
    _ = mixedMoment B node581 node581Labels := by rfl

def raw21222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21222 raw21222Labels = mixedMoment B node589 node589Labels := by
  calc
    mixedMoment B raw21222 raw21222Labels = mixedMoment B raw21222step0 raw21222step0Labels := by
      have hz : ∀ j, raw21222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21222step0 = (fun i j => raw21222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21222step0 raw21222; decide +kernel
      have hl : raw21222step0Labels = raw21222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21222 raw21222Labels permutation434 hz
    mixedMoment B raw21222step0 raw21222step0Labels = mixedMoment B raw21222step1 raw21222step1Labels := by
      have hz : ∀ j, raw21222step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21222step1 = (fun i j => raw21222step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21222step1 raw21222step0; decide +kernel
      have hl : raw21222step1Labels = raw21222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21222step0 raw21222step0Labels permutation80 hz
    _ = mixedMoment B node589 node589Labels := by rfl

def raw21223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21223step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21223 raw21223Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw21223 raw21223Labels = mixedMoment B raw21223step0 raw21223step0Labels := by
      have hz : ∀ j, raw21223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21223step0 = (fun i j => raw21223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21223step0 raw21223; decide +kernel
      have hl : raw21223step0Labels = raw21223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21223 raw21223Labels permutation434 hz
    mixedMoment B raw21223step0 raw21223step0Labels = mixedMoment B raw21223step1 raw21223step1Labels := by
      have hz : ∀ j, raw21223step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21223step1 = (fun i j => raw21223step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21223step1 raw21223step0; decide +kernel
      have hl : raw21223step1Labels = raw21223step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21223step0 raw21223step0Labels permutation80 hz
    _ = mixedMoment B node587 node587Labels := by rfl

def raw21224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21224step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21224 raw21224Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw21224 raw21224Labels = mixedMoment B raw21224step0 raw21224step0Labels := by
      have hz : ∀ j, raw21224 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21224step0 = (fun i j => raw21224 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21224step0 raw21224; decide +kernel
      have hl : raw21224step0Labels = raw21224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21224 raw21224Labels permutation434 hz
    mixedMoment B raw21224step0 raw21224step0Labels = mixedMoment B raw21224step1 raw21224step1Labels := by
      have ha : raw21224step1 = (fun i j => raw21224step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21224step1 raw21224step0; decide +kernel
      have hl : raw21224step1Labels = raw21224step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21224step0 raw21224step0Labels permutation38 permutation2
    _ = mixedMoment B node930 node930Labels := by rfl

def raw21225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21225step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21225 raw21225Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw21225 raw21225Labels = mixedMoment B raw21225step0 raw21225step0Labels := by
      have hz : ∀ j, raw21225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21225step0 = (fun i j => raw21225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21225step0 raw21225; decide +kernel
      have hl : raw21225step0Labels = raw21225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21225 raw21225Labels permutation346 hz
    mixedMoment B raw21225step0 raw21225step0Labels = mixedMoment B raw21225step1 raw21225step1Labels := by
      have ha : raw21225step1 = (fun i j => raw21225step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21225step1 raw21225step0; decide +kernel
      have hl : raw21225step1Labels = raw21225step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21225step0 raw21225step0Labels permutation38 permutation2
    _ = mixedMoment B node930 node930Labels := by rfl

def raw21226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw21226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw21226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21226 raw21226Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw21226 raw21226Labels = mixedMoment B raw21226step0 raw21226step0Labels := by
      have hz : ∀ j, raw21226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21226step0 = (fun i j => raw21226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21226step0 raw21226; decide +kernel
      have hl : raw21226step0Labels = raw21226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21226 raw21226Labels permutation434 hz
    mixedMoment B raw21226step0 raw21226step0Labels = mixedMoment B raw21226step1 raw21226step1Labels := by
      have hz : ∀ j, raw21226step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21226step1 = (fun i j => raw21226step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21226step1 raw21226step0; decide +kernel
      have hl : raw21226step1Labels = raw21226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21226step0 raw21226step0Labels permutation80 hz
    mixedMoment B raw21226step1 raw21226step1Labels = mixedMoment B raw21226step2 raw21226step2Labels := by
      have ha : raw21226step2 = (fun i j => raw21226step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21226step2 raw21226step1; decide +kernel
      have hl : raw21226step2Labels = raw21226step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21226step1 raw21226step1Labels permutation10 permutation2
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw21227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21227 raw21227Labels = mixedMoment B node1086 node1086Labels := by
  calc
    mixedMoment B raw21227 raw21227Labels = mixedMoment B raw21227step0 raw21227step0Labels := by
      have hz : ∀ j, raw21227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21227step0 = (fun i j => raw21227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21227step0 raw21227; decide +kernel
      have hl : raw21227step0Labels = raw21227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21227 raw21227Labels permutation434 hz
    mixedMoment B raw21227step0 raw21227step0Labels = mixedMoment B raw21227step1 raw21227step1Labels := by
      have hz : ∀ j, raw21227step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21227step1 = (fun i j => raw21227step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21227step1 raw21227step0; decide +kernel
      have hl : raw21227step1Labels = raw21227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21227step0 raw21227step0Labels permutation80 hz
    _ = mixedMoment B node1086 node1086Labels := by rfl

def raw21228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21228 raw21228Labels = mixedMoment B node945 node945Labels := by
  calc
    mixedMoment B raw21228 raw21228Labels = mixedMoment B raw21228step0 raw21228step0Labels := by
      have hz : ∀ j, raw21228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21228step0 = (fun i j => raw21228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21228step0 raw21228; decide +kernel
      have hl : raw21228step0Labels = raw21228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21228 raw21228Labels permutation434 hz
    _ = mixedMoment B node945 node945Labels := by rfl

def raw21229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21229 raw21229Labels = mixedMoment B node945 node945Labels := by
  calc
    mixedMoment B raw21229 raw21229Labels = mixedMoment B raw21229step0 raw21229step0Labels := by
      have hz : ∀ j, raw21229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21229step0 = (fun i j => raw21229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21229step0 raw21229; decide +kernel
      have hl : raw21229step0Labels = raw21229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21229 raw21229Labels permutation346 hz
    _ = mixedMoment B node945 node945Labels := by rfl

def raw21230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21230 raw21230Labels = mixedMoment B node953 node953Labels := by
  calc
    mixedMoment B raw21230 raw21230Labels = mixedMoment B raw21230step0 raw21230step0Labels := by
      have hz : ∀ j, raw21230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21230step0 = (fun i j => raw21230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21230step0 raw21230; decide +kernel
      have hl : raw21230step0Labels = raw21230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21230 raw21230Labels permutation434 hz
    mixedMoment B raw21230step0 raw21230step0Labels = mixedMoment B raw21230step1 raw21230step1Labels := by
      have hz : ∀ j, raw21230step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21230step1 = (fun i j => raw21230step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21230step1 raw21230step0; decide +kernel
      have hl : raw21230step1Labels = raw21230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21230step0 raw21230step0Labels permutation80 hz
    _ = mixedMoment B node953 node953Labels := by rfl

def raw21231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21231step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21231step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21231 raw21231Labels = mixedMoment B node951 node951Labels := by
  calc
    mixedMoment B raw21231 raw21231Labels = mixedMoment B raw21231step0 raw21231step0Labels := by
      have hz : ∀ j, raw21231 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21231step0 = (fun i j => raw21231 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21231step0 raw21231; decide +kernel
      have hl : raw21231step0Labels = raw21231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21231 raw21231Labels permutation434 hz
    mixedMoment B raw21231step0 raw21231step0Labels = mixedMoment B raw21231step1 raw21231step1Labels := by
      have hz : ∀ j, raw21231step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21231step1 = (fun i j => raw21231step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21231step1 raw21231step0; decide +kernel
      have hl : raw21231step1Labels = raw21231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21231step0 raw21231step0Labels permutation80 hz
    _ = mixedMoment B node951 node951Labels := by rfl

def raw21232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21232step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21232 raw21232Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw21232 raw21232Labels = mixedMoment B raw21232step0 raw21232step0Labels := by
      have hz : ∀ j, raw21232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21232step0 = (fun i j => raw21232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21232step0 raw21232; decide +kernel
      have hl : raw21232step0Labels = raw21232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21232 raw21232Labels permutation434 hz
    mixedMoment B raw21232step0 raw21232step0Labels = mixedMoment B raw21232step1 raw21232step1Labels := by
      have ha : raw21232step1 = (fun i j => raw21232step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21232step1 raw21232step0; decide +kernel
      have hl : raw21232step1Labels = raw21232step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21232step0 raw21232step0Labels permutation38 permutation2
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw21233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21233 raw21233Labels = mixedMoment B node905 node905Labels := by
  calc
    mixedMoment B raw21233 raw21233Labels = mixedMoment B raw21233step0 raw21233step0Labels := by
      have ha : raw21233step0 = (fun i j => raw21233 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21233step0 raw21233; decide +kernel
      have hl : raw21233step0Labels = raw21233Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21233 raw21233Labels permutation176 permutation2
    _ = mixedMoment B node905 node905Labels := by rfl

def raw21234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw21234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21234 raw21234Labels = mixedMoment B node913 node913Labels := by
  calc
    mixedMoment B raw21234 raw21234Labels = mixedMoment B raw21234step0 raw21234step0Labels := by
      have hz : ∀ j, raw21234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21234step0 = (fun i j => raw21234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21234step0 raw21234; decide +kernel
      have hl : raw21234step0Labels = raw21234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21234 raw21234Labels permutation434 hz
    mixedMoment B raw21234step0 raw21234step0Labels = mixedMoment B raw21234step1 raw21234step1Labels := by
      have ha : raw21234step1 = (fun i j => raw21234step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21234step1 raw21234step0; decide +kernel
      have hl : raw21234step1Labels = raw21234step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21234step0 raw21234step0Labels permutation38 permutation2
    _ = mixedMoment B node913 node913Labels := by rfl

def raw21235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21235step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21235 raw21235Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw21235 raw21235Labels = mixedMoment B raw21235step0 raw21235step0Labels := by
      have hz : ∀ j, raw21235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21235step0 = (fun i j => raw21235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21235step0 raw21235; decide +kernel
      have hl : raw21235step0Labels = raw21235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21235 raw21235Labels permutation434 hz
    mixedMoment B raw21235step0 raw21235step0Labels = mixedMoment B raw21235step1 raw21235step1Labels := by
      have ha : raw21235step1 = (fun i j => raw21235step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21235step1 raw21235step0; decide +kernel
      have hl : raw21235step1Labels = raw21235step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21235step0 raw21235step0Labels permutation38 permutation2
    _ = mixedMoment B node911 node911Labels := by rfl

def raw21236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21236step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21236step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21236 raw21236Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw21236 raw21236Labels = mixedMoment B raw21236step0 raw21236step0Labels := by
      have hz : ∀ j, raw21236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21236step0 = (fun i j => raw21236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21236step0 raw21236; decide +kernel
      have hl : raw21236step0Labels = raw21236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21236 raw21236Labels permutation434 hz
    mixedMoment B raw21236step0 raw21236step0Labels = mixedMoment B raw21236step1 raw21236step1Labels := by
      have ha : raw21236step1 = (fun i j => raw21236step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21236step1 raw21236step0; decide +kernel
      have hl : raw21236step1Labels = raw21236step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21236step0 raw21236step0Labels permutation38 permutation3
    mixedMoment B raw21236step1 raw21236step1Labels = mixedMoment B raw21236step2 raw21236step2Labels := by
      have ha : raw21236step2 = raw21236step1 := by apply Matrix.ext; unfold raw21236step2 raw21236step1; decide +kernel
      have hl : raw21236step1Labels = labelEmbedding6 ∘ raw21236step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21236step1 raw21236step1Labels raw21236step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw21237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21237step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21237 raw21237Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw21237 raw21237Labels = mixedMoment B raw21237step0 raw21237step0Labels := by
      have hz : ∀ j, raw21237 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21237step0 = (fun i j => raw21237 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21237step0 raw21237; decide +kernel
      have hl : raw21237step0Labels = raw21237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21237 raw21237Labels permutation346 hz
    mixedMoment B raw21237step0 raw21237step0Labels = mixedMoment B raw21237step1 raw21237step1Labels := by
      have ha : raw21237step1 = (fun i j => raw21237step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21237step1 raw21237step0; decide +kernel
      have hl : raw21237step1Labels = raw21237step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21237step0 raw21237step0Labels permutation38 permutation3
    mixedMoment B raw21237step1 raw21237step1Labels = mixedMoment B raw21237step2 raw21237step2Labels := by
      have ha : raw21237step2 = raw21237step1 := by apply Matrix.ext; unfold raw21237step2 raw21237step1; decide +kernel
      have hl : raw21237step1Labels = labelEmbedding6 ∘ raw21237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21237step1 raw21237step1Labels raw21237step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw21238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw21238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21238step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![3, -1, -2]]
def raw21238step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21238step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw21238step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21238step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw21238step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21238 raw21238Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw21238 raw21238Labels = mixedMoment B raw21238step0 raw21238step0Labels := by
      have hz : ∀ j, raw21238 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21238step0 = (fun i j => raw21238 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21238step0 raw21238; decide +kernel
      have hl : raw21238step0Labels = raw21238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21238 raw21238Labels permutation520 hz
    mixedMoment B raw21238step0 raw21238step0Labels = mixedMoment B raw21238step1 raw21238step1Labels := by
      have hz : ∀ j, raw21238step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21238step1 = (fun i j => raw21238step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21238step1 raw21238step0; decide +kernel
      have hl : raw21238step1Labels = raw21238step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21238step0 raw21238step0Labels permutation104 hz
    mixedMoment B raw21238step1 raw21238step1Labels = mixedMoment B raw21238step2 raw21238step2Labels := by
      have hz : ∀ j, raw21238step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21238step2 = (fun i j => raw21238step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21238step2 raw21238step1; decide +kernel
      have hl : raw21238step2Labels = raw21238step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21238step1 raw21238step1Labels permutation20 hz
    mixedMoment B raw21238step2 raw21238step2Labels = mixedMoment B raw21238step3 raw21238step3Labels := by
      have ha : raw21238step3 = (fun i j => raw21238step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21238step3 raw21238step2; decide +kernel
      have hl : raw21238step3Labels = raw21238step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21238step2 raw21238step2Labels permutation7 permutation2
    mixedMoment B raw21238step3 raw21238step3Labels = mixedMoment B raw21238step4 raw21238step4Labels := by
      have ha : raw21238step4 = -raw21238step3 := by apply Matrix.ext; change ∀ i j, raw21238step4 i j = -(raw21238step3 i j); unfold raw21238step4 raw21238step3; decide +kernel
      have hl : raw21238step4Labels = raw21238step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw21239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21239step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21239step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21239step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21239 raw21239Labels = mixedMoment B node4128 node4128Labels := by
  calc
    mixedMoment B raw21239 raw21239Labels = mixedMoment B raw21239step0 raw21239step0Labels := by
      have hz : ∀ j, raw21239 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21239step0 = (fun i j => raw21239 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21239step0 raw21239; decide +kernel
      have hl : raw21239step0Labels = raw21239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21239 raw21239Labels permutation434 hz
    mixedMoment B raw21239step0 raw21239step0Labels = mixedMoment B raw21239step1 raw21239step1Labels := by
      have hz : ∀ j, raw21239step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21239step1 = (fun i j => raw21239step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21239step1 raw21239step0; decide +kernel
      have hl : raw21239step1Labels = raw21239step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21239step0 raw21239step0Labels permutation80 hz
    mixedMoment B raw21239step1 raw21239step1Labels = mixedMoment B raw21239step2 raw21239step2Labels := by
      have ha : raw21239step2 = (fun i j => raw21239step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21239step2 raw21239step1; decide +kernel
      have hl : raw21239step2Labels = raw21239step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21239step1 raw21239step1Labels permutation10 permutation3
    mixedMoment B raw21239step2 raw21239step2Labels = mixedMoment B raw21239step3 raw21239step3Labels := by
      have ha : raw21239step3 = raw21239step2 := by apply Matrix.ext; unfold raw21239step3 raw21239step2; decide +kernel
      have hl : raw21239step2Labels = labelEmbedding6 ∘ raw21239step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21239step2 raw21239step2Labels raw21239step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4128 node4128Labels := by rfl

def raw21240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21240step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21240step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21240 raw21240Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21240 raw21240Labels = mixedMoment B raw21240step0 raw21240step0Labels := by
      have hz : ∀ j, raw21240 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21240step0 = (fun i j => raw21240 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21240step0 raw21240; decide +kernel
      have hl : raw21240step0Labels = raw21240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21240 raw21240Labels permutation434 hz
    mixedMoment B raw21240step0 raw21240step0Labels = mixedMoment B raw21240step1 raw21240step1Labels := by
      have ha : raw21240step1 = (fun i j => raw21240step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21240step1 raw21240step0; decide +kernel
      have hl : raw21240step1Labels = raw21240step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21240step0 raw21240step0Labels permutation40 permutation3
    mixedMoment B raw21240step1 raw21240step1Labels = mixedMoment B raw21240step2 raw21240step2Labels := by
      have ha : raw21240step2 = raw21240step1 := by apply Matrix.ext; unfold raw21240step2 raw21240step1; decide +kernel
      have hl : raw21240step1Labels = labelEmbedding6 ∘ raw21240step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21240step1 raw21240step1Labels raw21240step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw21241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21241step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21241 raw21241Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21241 raw21241Labels = mixedMoment B raw21241step0 raw21241step0Labels := by
      have hz : ∀ j, raw21241 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21241step0 = (fun i j => raw21241 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21241step0 raw21241; decide +kernel
      have hl : raw21241step0Labels = raw21241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21241 raw21241Labels permutation346 hz
    mixedMoment B raw21241step0 raw21241step0Labels = mixedMoment B raw21241step1 raw21241step1Labels := by
      have ha : raw21241step1 = (fun i j => raw21241step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21241step1 raw21241step0; decide +kernel
      have hl : raw21241step1Labels = raw21241step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21241step0 raw21241step0Labels permutation40 permutation3
    mixedMoment B raw21241step1 raw21241step1Labels = mixedMoment B raw21241step2 raw21241step2Labels := by
      have ha : raw21241step2 = raw21241step1 := by apply Matrix.ext; unfold raw21241step2 raw21241step1; decide +kernel
      have hl : raw21241step1Labels = labelEmbedding6 ∘ raw21241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21241step1 raw21241step1Labels raw21241step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw21242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![3, -1, -2]]
def raw21242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21242step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw21242step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21242step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw21242step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21242step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw21242step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21242 raw21242Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw21242 raw21242Labels = mixedMoment B raw21242step0 raw21242step0Labels := by
      have hz : ∀ j, raw21242 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21242step0 = (fun i j => raw21242 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21242step0 raw21242; decide +kernel
      have hl : raw21242step0Labels = raw21242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21242 raw21242Labels permutation520 hz
    mixedMoment B raw21242step0 raw21242step0Labels = mixedMoment B raw21242step1 raw21242step1Labels := by
      have hz : ∀ j, raw21242step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21242step1 = (fun i j => raw21242step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21242step1 raw21242step0; decide +kernel
      have hl : raw21242step1Labels = raw21242step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21242step0 raw21242step0Labels permutation104 hz
    mixedMoment B raw21242step1 raw21242step1Labels = mixedMoment B raw21242step2 raw21242step2Labels := by
      have hz : ∀ j, raw21242step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21242step2 = (fun i j => raw21242step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21242step2 raw21242step1; decide +kernel
      have hl : raw21242step2Labels = raw21242step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21242step1 raw21242step1Labels permutation20 hz
    mixedMoment B raw21242step2 raw21242step2Labels = mixedMoment B raw21242step3 raw21242step3Labels := by
      have ha : raw21242step3 = (fun i j => raw21242step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21242step3 raw21242step2; decide +kernel
      have hl : raw21242step3Labels = raw21242step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21242step2 raw21242step2Labels permutation2 permutation3
    mixedMoment B raw21242step3 raw21242step3Labels = mixedMoment B raw21242step4 raw21242step4Labels := by
      have ha : raw21242step4 = raw21242step3 := by apply Matrix.ext; unfold raw21242step4 raw21242step3; decide +kernel
      have hl : raw21242step3Labels = labelEmbedding6 ∘ raw21242step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21242step3 raw21242step3Labels raw21242step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4507 node4507Labels := by rfl

def raw21243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw21243step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21243step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw21243step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21243 raw21243Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw21243 raw21243Labels = mixedMoment B raw21243step0 raw21243step0Labels := by
      have hz : ∀ j, raw21243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21243step0 = (fun i j => raw21243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21243step0 raw21243; decide +kernel
      have hl : raw21243step0Labels = raw21243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21243 raw21243Labels permutation434 hz
    mixedMoment B raw21243step0 raw21243step0Labels = mixedMoment B raw21243step1 raw21243step1Labels := by
      have hz : ∀ j, raw21243step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21243step1 = (fun i j => raw21243step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21243step1 raw21243step0; decide +kernel
      have hl : raw21243step1Labels = raw21243step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21243step0 raw21243step0Labels permutation80 hz
    mixedMoment B raw21243step1 raw21243step1Labels = mixedMoment B raw21243step2 raw21243step2Labels := by
      have ha : raw21243step2 = (fun i j => raw21243step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21243step2 raw21243step1; decide +kernel
      have hl : raw21243step2Labels = raw21243step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21243step1 raw21243step1Labels permutation10 permutation3
    mixedMoment B raw21243step2 raw21243step2Labels = mixedMoment B raw21243step3 raw21243step3Labels := by
      have ha : raw21243step3 = raw21243step2 := by apply Matrix.ext; unfold raw21243step3 raw21243step2; decide +kernel
      have hl : raw21243step2Labels = labelEmbedding6 ∘ raw21243step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21243step2 raw21243step2Labels raw21243step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw21244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21244step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21244step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21244 raw21244Labels = mixedMoment B node4105 node4105Labels := by
  calc
    mixedMoment B raw21244 raw21244Labels = mixedMoment B raw21244step0 raw21244step0Labels := by
      have hz : ∀ j, raw21244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21244step0 = (fun i j => raw21244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21244step0 raw21244; decide +kernel
      have hl : raw21244step0Labels = raw21244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21244 raw21244Labels permutation434 hz
    mixedMoment B raw21244step0 raw21244step0Labels = mixedMoment B raw21244step1 raw21244step1Labels := by
      have ha : raw21244step1 = (fun i j => raw21244step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21244step1 raw21244step0; decide +kernel
      have hl : raw21244step1Labels = raw21244step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21244step0 raw21244step0Labels permutation32 permutation3
    mixedMoment B raw21244step1 raw21244step1Labels = mixedMoment B raw21244step2 raw21244step2Labels := by
      have ha : raw21244step2 = raw21244step1 := by apply Matrix.ext; unfold raw21244step2 raw21244step1; decide +kernel
      have hl : raw21244step1Labels = labelEmbedding6 ∘ raw21244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21244step1 raw21244step1Labels raw21244step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4105 node4105Labels := by rfl

def raw21245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21245step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21245 raw21245Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw21245 raw21245Labels = mixedMoment B raw21245step0 raw21245step0Labels := by
      have hz : ∀ j, raw21245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21245step0 = (fun i j => raw21245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21245step0 raw21245; decide +kernel
      have hl : raw21245step0Labels = raw21245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21245 raw21245Labels permutation434 hz
    mixedMoment B raw21245step0 raw21245step0Labels = mixedMoment B raw21245step1 raw21245step1Labels := by
      have ha : raw21245step1 = (fun i j => raw21245step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21245step1 raw21245step0; decide +kernel
      have hl : raw21245step1Labels = raw21245step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21245step0 raw21245step0Labels permutation32 permutation3
    mixedMoment B raw21245step1 raw21245step1Labels = mixedMoment B raw21245step2 raw21245step2Labels := by
      have ha : raw21245step2 = raw21245step1 := by apply Matrix.ext; unfold raw21245step2 raw21245step1; decide +kernel
      have hl : raw21245step1Labels = labelEmbedding6 ∘ raw21245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21245step1 raw21245step1Labels raw21245step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4352 node4352Labels := by rfl

def raw21246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21246step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21246 raw21246Labels = mixedMoment B node4290 node4290Labels := by
  calc
    mixedMoment B raw21246 raw21246Labels = mixedMoment B raw21246step0 raw21246step0Labels := by
      have ha : raw21246step0 = (fun i j => raw21246 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21246step0 raw21246; decide +kernel
      have hl : raw21246step0Labels = raw21246Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21246 raw21246Labels permutation200 permutation3
    mixedMoment B raw21246step0 raw21246step0Labels = mixedMoment B raw21246step1 raw21246step1Labels := by
      have ha : raw21246step1 = raw21246step0 := by apply Matrix.ext; unfold raw21246step1 raw21246step0; decide +kernel
      have hl : raw21246step0Labels = labelEmbedding6 ∘ raw21246step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21246step0 raw21246step0Labels raw21246step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4290 node4290Labels := by rfl

def raw21247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21247step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21247step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21247step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21247step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21247 raw21247Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21247 raw21247Labels = mixedMoment B raw21247step0 raw21247step0Labels := by
      have hz : ∀ j, raw21247 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21247step0 = (fun i j => raw21247 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21247step0 raw21247; decide +kernel
      have hl : raw21247step0Labels = raw21247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21247 raw21247Labels permutation520 hz
    mixedMoment B raw21247step0 raw21247step0Labels = mixedMoment B raw21247step1 raw21247step1Labels := by
      have hz : ∀ j, raw21247step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21247step1 = (fun i j => raw21247step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21247step1 raw21247step0; decide +kernel
      have hl : raw21247step1Labels = raw21247step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21247step0 raw21247step0Labels permutation104 hz
    mixedMoment B raw21247step1 raw21247step1Labels = mixedMoment B raw21247step2 raw21247step2Labels := by
      have ha : raw21247step2 = (fun i j => raw21247step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21247step2 raw21247step1; decide +kernel
      have hl : raw21247step2Labels = raw21247step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21247step1 raw21247step1Labels permutation8 permutation3
    mixedMoment B raw21247step2 raw21247step2Labels = mixedMoment B raw21247step3 raw21247step3Labels := by
      have ha : raw21247step3 = raw21247step2 := by apply Matrix.ext; unfold raw21247step3 raw21247step2; decide +kernel
      have hl : raw21247step2Labels = labelEmbedding6 ∘ raw21247step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21247step2 raw21247step2Labels raw21247step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
