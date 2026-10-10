import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24064 raw24064Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw24064 raw24064Labels = mixedMoment B raw24064step0 raw24064step0Labels := by
      have ha : raw24064step0 = (fun i j => raw24064 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24064step0 raw24064; decide +kernel
      have hl : raw24064step0Labels = raw24064Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24064 raw24064Labels permutation178 permutation2
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw24065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24065 raw24065Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw24065 raw24065Labels = mixedMoment B raw24065step0 raw24065step0Labels := by
      have ha : raw24065step0 = (fun i j => raw24065 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24065step0 raw24065; decide +kernel
      have hl : raw24065step0Labels = raw24065Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24065 raw24065Labels permutation176 permutation2
    _ = mixedMoment B node2671 node2671Labels := by rfl

def raw24066 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw24066Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24066step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw24066step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24066 raw24066Labels = mixedMoment B node4087 node4087Labels := by
  calc
    mixedMoment B raw24066 raw24066Labels = mixedMoment B raw24066step0 raw24066step0Labels := by
      have ha : raw24066step0 = (fun i j => raw24066 (permutation176 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24066step0 raw24066; decide +kernel
      have hl : raw24066step0Labels = raw24066Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24066 raw24066Labels permutation176 permutation0
    _ = mixedMoment B node4087 node4087Labels := by rfl

def raw24067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24067 raw24067Labels = mixedMoment B node1187 node1187Labels := by
  calc
    mixedMoment B raw24067 raw24067Labels = mixedMoment B raw24067step0 raw24067step0Labels := by
      have ha : raw24067step0 = (fun i j => raw24067 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24067step0 raw24067; decide +kernel
      have hl : raw24067step0Labels = raw24067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24067 raw24067Labels permutation176 permutation2
    _ = mixedMoment B node1187 node1187Labels := by rfl

def raw24068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24068 raw24068Labels = mixedMoment B node1256 node1256Labels := by
  calc
    _ = mixedMoment B node1256 node1256Labels := by rfl

def raw24069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24069 raw24069Labels = mixedMoment B node1180 node1180Labels := by
  calc
    mixedMoment B raw24069 raw24069Labels = mixedMoment B raw24069step0 raw24069step0Labels := by
      have ha : raw24069step0 = (fun i j => raw24069 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24069step0 raw24069; decide +kernel
      have hl : raw24069step0Labels = raw24069Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24069 raw24069Labels permutation179 permutation2
    _ = mixedMoment B node1180 node1180Labels := by rfl

def raw24070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw24070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24070 raw24070Labels = mixedMoment B node1180 node1180Labels := by
  calc
    mixedMoment B raw24070 raw24070Labels = mixedMoment B raw24070step0 raw24070step0Labels := by
      have ha : raw24070step0 = (fun i j => raw24070 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24070step0 raw24070; decide +kernel
      have hl : raw24070step0Labels = raw24070Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24070 raw24070Labels permutation177 permutation2
    _ = mixedMoment B node1180 node1180Labels := by rfl

def raw24071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24071 raw24071Labels = mixedMoment B node1178 node1178Labels := by
  calc
    mixedMoment B raw24071 raw24071Labels = mixedMoment B raw24071step0 raw24071step0Labels := by
      have ha : raw24071step0 = (fun i j => raw24071 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24071step0 raw24071; decide +kernel
      have hl : raw24071step0Labels = raw24071Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24071 raw24071Labels permutation178 permutation2
    _ = mixedMoment B node1178 node1178Labels := by rfl

def raw24072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24072 raw24072Labels = mixedMoment B node2606 node2606Labels := by
  calc
    mixedMoment B raw24072 raw24072Labels = mixedMoment B raw24072step0 raw24072step0Labels := by
      have ha : raw24072step0 = (fun i j => raw24072 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24072step0 raw24072; decide +kernel
      have hl : raw24072step0Labels = raw24072Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24072 raw24072Labels permutation154 permutation2
    _ = mixedMoment B node2606 node2606Labels := by rfl

def raw24073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24073 raw24073Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw24073 raw24073Labels = mixedMoment B raw24073step0 raw24073step0Labels := by
      have ha : raw24073step0 = (fun i j => raw24073 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24073step0 raw24073; decide +kernel
      have hl : raw24073step0Labels = raw24073Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24073 raw24073Labels permutation178 permutation2
    _ = mixedMoment B node2382 node2382Labels := by rfl

def raw24074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24074 raw24074Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw24074 raw24074Labels = mixedMoment B raw24074step0 raw24074step0Labels := by
      have ha : raw24074step0 = (fun i j => raw24074 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24074step0 raw24074; decide +kernel
      have hl : raw24074step0Labels = raw24074Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24074 raw24074Labels permutation176 permutation2
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw24075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw24075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24075 raw24075Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw24075 raw24075Labels = mixedMoment B raw24075step0 raw24075step0Labels := by
      have hz : ∀ j, raw24075 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24075step0 = (fun i j => raw24075 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24075step0 raw24075; decide +kernel
      have hl : raw24075step0Labels = raw24075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24075 raw24075Labels permutation520 hz
    mixedMoment B raw24075step0 raw24075step0Labels = mixedMoment B raw24075step1 raw24075step1Labels := by
      have ha : raw24075step1 = (fun i j => raw24075step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24075step1 raw24075step0; decide +kernel
      have hl : raw24075step1Labels = raw24075step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24075step0 raw24075step0Labels permutation38 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw24076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24076 raw24076Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw24076 raw24076Labels = mixedMoment B raw24076step0 raw24076step0Labels := by
      have ha : raw24076step0 = (fun i j => raw24076 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24076step0 raw24076; decide +kernel
      have hl : raw24076step0Labels = raw24076Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24076 raw24076Labels permutation178 permutation2
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw24077 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]
def raw24077Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24077step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![1, -1], ![2, -2]]
def raw24077step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24077step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24077step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24077 raw24077Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw24077 raw24077Labels = mixedMoment B raw24077step0 raw24077step0Labels := by
      have hz : ∀ j, raw24077 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24077step0 = (fun i j => raw24077 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24077step0 raw24077; decide +kernel
      have hl : raw24077step0Labels = raw24077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24077 raw24077Labels permutation520 hz
    mixedMoment B raw24077step0 raw24077step0Labels = mixedMoment B raw24077step1 raw24077step1Labels := by
      have ha : raw24077step1 = (fun i j => raw24077step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24077step1 raw24077step0; decide +kernel
      have hl : raw24077step1Labels = raw24077step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24077step0 raw24077step0Labels permutation38 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw24078 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw24078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24078 raw24078Labels = mixedMoment B node1656 node1656Labels := by
  calc
    mixedMoment B raw24078 raw24078Labels = mixedMoment B raw24078step0 raw24078step0Labels := by
      have hz : ∀ j, raw24078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24078step0 = (fun i j => raw24078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24078step0 raw24078; decide +kernel
      have hl : raw24078step0Labels = raw24078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24078 raw24078Labels permutation265 hz
    mixedMoment B raw24078step0 raw24078step0Labels = mixedMoment B raw24078step1 raw24078step1Labels := by
      have ha : raw24078step1 = (fun i j => raw24078step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24078step1 raw24078step0; decide +kernel
      have hl : raw24078step1Labels = raw24078step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24078step0 raw24078step0Labels permutation51 permutation2
    mixedMoment B raw24078step1 raw24078step1Labels = mixedMoment B raw24078step2 raw24078step2Labels := by
      have ha : raw24078step2 = -raw24078step1 := by apply Matrix.ext; change ∀ i j, raw24078step2 i j = -(raw24078step1 i j); unfold raw24078step2 raw24078step1; decide +kernel
      have hl : raw24078step2Labels = raw24078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1656 node1656Labels := by rfl

def raw24079 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw24079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24079step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw24079step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24079 raw24079Labels = mixedMoment B node1659 node1659Labels := by
  calc
    mixedMoment B raw24079 raw24079Labels = mixedMoment B raw24079step0 raw24079step0Labels := by
      have hz : ∀ j, raw24079 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24079step0 = (fun i j => raw24079 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24079step0 raw24079; decide +kernel
      have hl : raw24079step0Labels = raw24079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24079 raw24079Labels permutation346 hz
    mixedMoment B raw24079step0 raw24079step0Labels = mixedMoment B raw24079step1 raw24079step1Labels := by
      have hz : ∀ j, raw24079step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24079step1 = (fun i j => raw24079step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24079step1 raw24079step0; decide +kernel
      have hl : raw24079step1Labels = raw24079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24079step0 raw24079step0Labels permutation56 hz
    mixedMoment B raw24079step1 raw24079step1Labels = mixedMoment B raw24079step2 raw24079step2Labels := by
      have ha : raw24079step2 = (fun i j => raw24079step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24079step2 raw24079step1; decide +kernel
      have hl : raw24079step2Labels = raw24079step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24079step1 raw24079step1Labels permutation13 permutation2
    mixedMoment B raw24079step2 raw24079step2Labels = mixedMoment B raw24079step3 raw24079step3Labels := by
      have ha : raw24079step3 = -raw24079step2 := by apply Matrix.ext; change ∀ i j, raw24079step3 i j = -(raw24079step2 i j); unfold raw24079step3 raw24079step2; decide +kernel
      have hl : raw24079step3Labels = raw24079step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1659 node1659Labels := by rfl

def raw24080 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24080step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24080step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw24080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24080step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def raw24080step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24080 raw24080Labels = mixedMoment B node1661 node1661Labels := by
  calc
    mixedMoment B raw24080 raw24080Labels = mixedMoment B raw24080step0 raw24080step0Labels := by
      have hz : ∀ j, raw24080 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24080step0 = (fun i j => raw24080 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24080step0 raw24080; decide +kernel
      have hl : raw24080step0Labels = raw24080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24080 raw24080Labels permutation346 hz
    mixedMoment B raw24080step0 raw24080step0Labels = mixedMoment B raw24080step1 raw24080step1Labels := by
      have hz : ∀ j, raw24080step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24080step1 = (fun i j => raw24080step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24080step1 raw24080step0; decide +kernel
      have hl : raw24080step1Labels = raw24080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24080step0 raw24080step0Labels permutation56 hz
    mixedMoment B raw24080step1 raw24080step1Labels = mixedMoment B raw24080step2 raw24080step2Labels := by
      have ha : raw24080step2 = (fun i j => raw24080step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24080step2 raw24080step1; decide +kernel
      have hl : raw24080step2Labels = raw24080step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24080step1 raw24080step1Labels permutation12 permutation2
    mixedMoment B raw24080step2 raw24080step2Labels = mixedMoment B raw24080step3 raw24080step3Labels := by
      have ha : raw24080step3 = -raw24080step2 := by apply Matrix.ext; change ∀ i j, raw24080step3 i j = -(raw24080step2 i j); unfold raw24080step3 raw24080step2; decide +kernel
      have hl : raw24080step3Labels = raw24080step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1661 node1661Labels := by rfl

def raw24081 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24081step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24081 raw24081Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw24081 raw24081Labels = mixedMoment B raw24081step0 raw24081step0Labels := by
      have hz : ∀ j, raw24081 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24081step0 = (fun i j => raw24081 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24081step0 raw24081; decide +kernel
      have hl : raw24081step0Labels = raw24081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24081 raw24081Labels permutation346 hz
    mixedMoment B raw24081step0 raw24081step0Labels = mixedMoment B raw24081step1 raw24081step1Labels := by
      have hz : ∀ j, raw24081step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24081step1 = (fun i j => raw24081step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24081step1 raw24081step0; decide +kernel
      have hl : raw24081step1Labels = raw24081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24081step0 raw24081step0Labels permutation56 hz
    mixedMoment B raw24081step1 raw24081step1Labels = mixedMoment B raw24081step2 raw24081step2Labels := by
      have ha : raw24081step2 = (fun i j => raw24081step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24081step2 raw24081step1; decide +kernel
      have hl : raw24081step2Labels = raw24081step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24081step1 raw24081step1Labels permutation13 permutation2
    mixedMoment B raw24081step2 raw24081step2Labels = mixedMoment B raw24081step3 raw24081step3Labels := by
      have ha : raw24081step3 = -raw24081step2 := by apply Matrix.ext; change ∀ i j, raw24081step3 i j = -(raw24081step2 i j); unfold raw24081step3 raw24081step2; decide +kernel
      have hl : raw24081step3Labels = raw24081step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw24082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24082step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw24082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24082step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24082step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24082 raw24082Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw24082 raw24082Labels = mixedMoment B raw24082step0 raw24082step0Labels := by
      have hz : ∀ j, raw24082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24082step0 = (fun i j => raw24082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24082step0 raw24082; decide +kernel
      have hl : raw24082step0Labels = raw24082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24082 raw24082Labels permutation346 hz
    mixedMoment B raw24082step0 raw24082step0Labels = mixedMoment B raw24082step1 raw24082step1Labels := by
      have hz : ∀ j, raw24082step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24082step1 = (fun i j => raw24082step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24082step1 raw24082step0; decide +kernel
      have hl : raw24082step1Labels = raw24082step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24082step0 raw24082step0Labels permutation56 hz
    mixedMoment B raw24082step1 raw24082step1Labels = mixedMoment B raw24082step2 raw24082step2Labels := by
      have ha : raw24082step2 = (fun i j => raw24082step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24082step2 raw24082step1; decide +kernel
      have hl : raw24082step2Labels = raw24082step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24082step1 raw24082step1Labels permutation8 permutation4
    mixedMoment B raw24082step2 raw24082step2Labels = mixedMoment B raw24082step3 raw24082step3Labels := by
      have ha : raw24082step3 = -raw24082step2 := by apply Matrix.ext; change ∀ i j, raw24082step3 i j = -(raw24082step2 i j); unfold raw24082step3 raw24082step2; decide +kernel
      have hl : raw24082step3Labels = raw24082step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1650 node1650Labels := by rfl

def raw24083 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw24083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24083 raw24083Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw24083 raw24083Labels = mixedMoment B raw24083step0 raw24083step0Labels := by
      have hz : ∀ j, raw24083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24083step0 = (fun i j => raw24083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24083step0 raw24083; decide +kernel
      have hl : raw24083step0Labels = raw24083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24083 raw24083Labels permutation346 hz
    mixedMoment B raw24083step0 raw24083step0Labels = mixedMoment B raw24083step1 raw24083step1Labels := by
      have ha : raw24083step1 = (fun i j => raw24083step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24083step1 raw24083step0; decide +kernel
      have hl : raw24083step1Labels = raw24083step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24083step0 raw24083step0Labels permutation151 permutation4
    _ = mixedMoment B node2502 node2502Labels := by rfl

def raw24084 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw24084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24084 raw24084Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw24084 raw24084Labels = mixedMoment B raw24084step0 raw24084step0Labels := by
      have hz : ∀ j, raw24084 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24084step0 = (fun i j => raw24084 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24084step0 raw24084; decide +kernel
      have hl : raw24084step0Labels = raw24084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24084 raw24084Labels permutation265 hz
    mixedMoment B raw24084step0 raw24084step0Labels = mixedMoment B raw24084step1 raw24084step1Labels := by
      have ha : raw24084step1 = (fun i j => raw24084step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24084step1 raw24084step0; decide +kernel
      have hl : raw24084step1Labels = raw24084step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24084step0 raw24084step0Labels permutation151 permutation4
    _ = mixedMoment B node2502 node2502Labels := by rfl

def raw24085 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 2, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw24085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24085 raw24085Labels = mixedMoment B node2521 node2521Labels := by
  calc
    mixedMoment B raw24085 raw24085Labels = mixedMoment B raw24085step0 raw24085step0Labels := by
      have hz : ∀ j, raw24085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24085step0 = (fun i j => raw24085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24085step0 raw24085; decide +kernel
      have hl : raw24085step0Labels = raw24085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24085 raw24085Labels permutation346 hz
    mixedMoment B raw24085step0 raw24085step0Labels = mixedMoment B raw24085step1 raw24085step1Labels := by
      have hz : ∀ j, raw24085step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24085step1 = (fun i j => raw24085step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24085step1 raw24085step0; decide +kernel
      have hl : raw24085step1Labels = raw24085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24085step0 raw24085step0Labels permutation56 hz
    mixedMoment B raw24085step1 raw24085step1Labels = mixedMoment B raw24085step2 raw24085step2Labels := by
      have ha : raw24085step2 = (fun i j => raw24085step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24085step2 raw24085step1; decide +kernel
      have hl : raw24085step2Labels = raw24085step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24085step1 raw24085step1Labels permutation31 permutation4
    _ = mixedMoment B node2521 node2521Labels := by rfl

def raw24086 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24086step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24086step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24086step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24086 raw24086Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw24086 raw24086Labels = mixedMoment B raw24086step0 raw24086step0Labels := by
      have hz : ∀ j, raw24086 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24086step0 = (fun i j => raw24086 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24086step0 raw24086; decide +kernel
      have hl : raw24086step0Labels = raw24086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24086 raw24086Labels permutation346 hz
    mixedMoment B raw24086step0 raw24086step0Labels = mixedMoment B raw24086step1 raw24086step1Labels := by
      have hz : ∀ j, raw24086step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24086step1 = (fun i j => raw24086step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24086step1 raw24086step0; decide +kernel
      have hl : raw24086step1Labels = raw24086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24086step0 raw24086step0Labels permutation56 hz
    mixedMoment B raw24086step1 raw24086step1Labels = mixedMoment B raw24086step2 raw24086step2Labels := by
      have ha : raw24086step2 = (fun i j => raw24086step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24086step2 raw24086step1; decide +kernel
      have hl : raw24086step2Labels = raw24086step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24086step1 raw24086step1Labels permutation8 permutation4
    mixedMoment B raw24086step2 raw24086step2Labels = mixedMoment B raw24086step3 raw24086step3Labels := by
      have ha : raw24086step3 = -raw24086step2 := by apply Matrix.ext; change ∀ i j, raw24086step3 i j = -(raw24086step2 i j); unfold raw24086step3 raw24086step2; decide +kernel
      have hl : raw24086step3Labels = raw24086step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3305 node3305Labels := by rfl

def raw24087 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw24087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24087 raw24087Labels = mixedMoment B node1646 node1646Labels := by
  calc
    mixedMoment B raw24087 raw24087Labels = mixedMoment B raw24087step0 raw24087step0Labels := by
      have hz : ∀ j, raw24087 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24087step0 = (fun i j => raw24087 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24087step0 raw24087; decide +kernel
      have hl : raw24087step0Labels = raw24087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24087 raw24087Labels permutation265 hz
    mixedMoment B raw24087step0 raw24087step0Labels = mixedMoment B raw24087step1 raw24087step1Labels := by
      have ha : raw24087step1 = (fun i j => raw24087step0 (permutation45 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24087step1 raw24087step0; decide +kernel
      have hl : raw24087step1Labels = raw24087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24087step0 raw24087step0Labels permutation45 permutation2
    mixedMoment B raw24087step1 raw24087step1Labels = mixedMoment B raw24087step2 raw24087step2Labels := by
      have ha : raw24087step2 = -raw24087step1 := by apply Matrix.ext; change ∀ i j, raw24087step2 i j = -(raw24087step1 i j); unfold raw24087step2 raw24087step1; decide +kernel
      have hl : raw24087step2Labels = raw24087step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1646 node1646Labels := by rfl

def raw24088 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw24088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw24088step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24088 raw24088Labels = mixedMoment B node1651 node1651Labels := by
  calc
    mixedMoment B raw24088 raw24088Labels = mixedMoment B raw24088step0 raw24088step0Labels := by
      have hz : ∀ j, raw24088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24088step0 = (fun i j => raw24088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24088step0 raw24088; decide +kernel
      have hl : raw24088step0Labels = raw24088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24088 raw24088Labels permutation346 hz
    mixedMoment B raw24088step0 raw24088step0Labels = mixedMoment B raw24088step1 raw24088step1Labels := by
      have hz : ∀ j, raw24088step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24088step1 = (fun i j => raw24088step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24088step1 raw24088step0; decide +kernel
      have hl : raw24088step1Labels = raw24088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24088step0 raw24088step0Labels permutation56 hz
    mixedMoment B raw24088step1 raw24088step1Labels = mixedMoment B raw24088step2 raw24088step2Labels := by
      have ha : raw24088step2 = (fun i j => raw24088step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24088step2 raw24088step1; decide +kernel
      have hl : raw24088step2Labels = raw24088step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24088step1 raw24088step1Labels permutation11 permutation2
    mixedMoment B raw24088step2 raw24088step2Labels = mixedMoment B raw24088step3 raw24088step3Labels := by
      have ha : raw24088step3 = -raw24088step2 := by apply Matrix.ext; change ∀ i j, raw24088step3 i j = -(raw24088step2 i j); unfold raw24088step3 raw24088step2; decide +kernel
      have hl : raw24088step3Labels = raw24088step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1651 node1651Labels := by rfl

def raw24089 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24089step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24089step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24089 raw24089Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw24089 raw24089Labels = mixedMoment B raw24089step0 raw24089step0Labels := by
      have hz : ∀ j, raw24089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24089step0 = (fun i j => raw24089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24089step0 raw24089; decide +kernel
      have hl : raw24089step0Labels = raw24089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24089 raw24089Labels permutation346 hz
    mixedMoment B raw24089step0 raw24089step0Labels = mixedMoment B raw24089step1 raw24089step1Labels := by
      have hz : ∀ j, raw24089step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24089step1 = (fun i j => raw24089step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24089step1 raw24089step0; decide +kernel
      have hl : raw24089step1Labels = raw24089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24089step0 raw24089step0Labels permutation56 hz
    mixedMoment B raw24089step1 raw24089step1Labels = mixedMoment B raw24089step2 raw24089step2Labels := by
      have ha : raw24089step2 = (fun i j => raw24089step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24089step2 raw24089step1; decide +kernel
      have hl : raw24089step2Labels = raw24089step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24089step1 raw24089step1Labels permutation11 permutation2
    mixedMoment B raw24089step2 raw24089step2Labels = mixedMoment B raw24089step3 raw24089step3Labels := by
      have ha : raw24089step3 = -raw24089step2 := by apply Matrix.ext; change ∀ i j, raw24089step3 i j = -(raw24089step2 i j); unfold raw24089step3 raw24089step2; decide +kernel
      have hl : raw24089step3Labels = raw24089step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw24090 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw24090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24090step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24090step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24090 raw24090Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw24090 raw24090Labels = mixedMoment B raw24090step0 raw24090step0Labels := by
      have hz : ∀ j, raw24090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24090step0 = (fun i j => raw24090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24090step0 raw24090; decide +kernel
      have hl : raw24090step0Labels = raw24090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24090 raw24090Labels permutation346 hz
    mixedMoment B raw24090step0 raw24090step0Labels = mixedMoment B raw24090step1 raw24090step1Labels := by
      have hz : ∀ j, raw24090step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24090step1 = (fun i j => raw24090step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24090step1 raw24090step0; decide +kernel
      have hl : raw24090step1Labels = raw24090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24090step0 raw24090step0Labels permutation56 hz
    mixedMoment B raw24090step1 raw24090step1Labels = mixedMoment B raw24090step2 raw24090step2Labels := by
      have ha : raw24090step2 = (fun i j => raw24090step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24090step2 raw24090step1; decide +kernel
      have hl : raw24090step2Labels = raw24090step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24090step1 raw24090step1Labels permutation10 permutation2
    mixedMoment B raw24090step2 raw24090step2Labels = mixedMoment B raw24090step3 raw24090step3Labels := by
      have ha : raw24090step3 = -raw24090step2 := by apply Matrix.ext; change ∀ i j, raw24090step3 i j = -(raw24090step2 i j); unfold raw24090step3 raw24090step2; decide +kernel
      have hl : raw24090step3Labels = raw24090step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1653 node1653Labels := by rfl

def raw24091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw24091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24091step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24091 raw24091Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw24091 raw24091Labels = mixedMoment B raw24091step0 raw24091step0Labels := by
      have hz : ∀ j, raw24091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24091step0 = (fun i j => raw24091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24091step0 raw24091; decide +kernel
      have hl : raw24091step0Labels = raw24091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24091 raw24091Labels permutation346 hz
    mixedMoment B raw24091step0 raw24091step0Labels = mixedMoment B raw24091step1 raw24091step1Labels := by
      have hz : ∀ j, raw24091step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24091step1 = (fun i j => raw24091step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24091step1 raw24091step0; decide +kernel
      have hl : raw24091step1Labels = raw24091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24091step0 raw24091step0Labels permutation56 hz
    mixedMoment B raw24091step1 raw24091step1Labels = mixedMoment B raw24091step2 raw24091step2Labels := by
      have ha : raw24091step2 = (fun i j => raw24091step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24091step2 raw24091step1; decide +kernel
      have hl : raw24091step2Labels = raw24091step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24091step1 raw24091step1Labels permutation8 permutation4
    mixedMoment B raw24091step2 raw24091step2Labels = mixedMoment B raw24091step3 raw24091step3Labels := by
      have ha : raw24091step3 = -raw24091step2 := by apply Matrix.ext; change ∀ i j, raw24091step3 i j = -(raw24091step2 i j); unfold raw24091step3 raw24091step2; decide +kernel
      have hl : raw24091step3Labels = raw24091step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1653 node1653Labels := by rfl

def raw24092 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw24092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24092 raw24092Labels = mixedMoment B node3287 node3287Labels := by
  calc
    mixedMoment B raw24092 raw24092Labels = mixedMoment B raw24092step0 raw24092step0Labels := by
      have hz : ∀ j, raw24092 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24092step0 = (fun i j => raw24092 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24092step0 raw24092; decide +kernel
      have hl : raw24092step0Labels = raw24092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24092 raw24092Labels permutation265 hz
    mixedMoment B raw24092step0 raw24092step0Labels = mixedMoment B raw24092step1 raw24092step1Labels := by
      have ha : raw24092step1 = (fun i j => raw24092step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24092step1 raw24092step0; decide +kernel
      have hl : raw24092step1Labels = raw24092step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24092step0 raw24092step0Labels permutation32 permutation4
    mixedMoment B raw24092step1 raw24092step1Labels = mixedMoment B raw24092step2 raw24092step2Labels := by
      have ha : raw24092step2 = -raw24092step1 := by apply Matrix.ext; change ∀ i j, raw24092step2 i j = -(raw24092step1 i j); unfold raw24092step2 raw24092step1; decide +kernel
      have hl : raw24092step2Labels = raw24092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3287 node3287Labels := by rfl

def raw24093 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 2, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 2, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw24093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24093 raw24093Labels = mixedMoment B node3049 node3049Labels := by
  calc
    mixedMoment B raw24093 raw24093Labels = mixedMoment B raw24093step0 raw24093step0Labels := by
      have hz : ∀ j, raw24093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24093step0 = (fun i j => raw24093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24093step0 raw24093; decide +kernel
      have hl : raw24093step0Labels = raw24093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24093 raw24093Labels permutation346 hz
    mixedMoment B raw24093step0 raw24093step0Labels = mixedMoment B raw24093step1 raw24093step1Labels := by
      have hz : ∀ j, raw24093step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24093step1 = (fun i j => raw24093step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24093step1 raw24093step0; decide +kernel
      have hl : raw24093step1Labels = raw24093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24093step0 raw24093step0Labels permutation56 hz
    mixedMoment B raw24093step1 raw24093step1Labels = mixedMoment B raw24093step2 raw24093step2Labels := by
      have ha : raw24093step2 = (fun i j => raw24093step1 (permutation19 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24093step2 raw24093step1; decide +kernel
      have hl : raw24093step2Labels = raw24093step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24093step1 raw24093step1Labels permutation19 permutation2
    _ = mixedMoment B node3049 node3049Labels := by rfl

def raw24094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24094 raw24094Labels = mixedMoment B node1288 node1288Labels := by
  calc
    mixedMoment B raw24094 raw24094Labels = mixedMoment B raw24094step0 raw24094step0Labels := by
      have hz : ∀ j, raw24094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24094step0 = (fun i j => raw24094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24094step0 raw24094; decide +kernel
      have hl : raw24094step0Labels = raw24094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24094 raw24094Labels permutation346 hz
    mixedMoment B raw24094step0 raw24094step0Labels = mixedMoment B raw24094step1 raw24094step1Labels := by
      have hz : ∀ j, raw24094step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24094step1 = (fun i j => raw24094step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24094step1 raw24094step0; decide +kernel
      have hl : raw24094step1Labels = raw24094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24094step0 raw24094step0Labels permutation56 hz
    mixedMoment B raw24094step1 raw24094step1Labels = mixedMoment B raw24094step2 raw24094step2Labels := by
      have ha : raw24094step2 = (fun i j => raw24094step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24094step2 raw24094step1; decide +kernel
      have hl : raw24094step2Labels = raw24094step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24094step1 raw24094step1Labels permutation10 permutation2
    _ = mixedMoment B node1288 node1288Labels := by rfl

def raw24095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24095 raw24095Labels = mixedMoment B node2585 node2585Labels := by
  calc
    mixedMoment B raw24095 raw24095Labels = mixedMoment B raw24095step0 raw24095step0Labels := by
      have hz : ∀ j, raw24095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24095step0 = (fun i j => raw24095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24095step0 raw24095; decide +kernel
      have hl : raw24095step0Labels = raw24095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24095 raw24095Labels permutation346 hz
    mixedMoment B raw24095step0 raw24095step0Labels = mixedMoment B raw24095step1 raw24095step1Labels := by
      have ha : raw24095step1 = (fun i j => raw24095step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24095step1 raw24095step0; decide +kernel
      have hl : raw24095step1Labels = raw24095step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24095step0 raw24095step0Labels permutation34 permutation2
    _ = mixedMoment B node2585 node2585Labels := by rfl

def raw24096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24096 raw24096Labels = mixedMoment B node2585 node2585Labels := by
  calc
    mixedMoment B raw24096 raw24096Labels = mixedMoment B raw24096step0 raw24096step0Labels := by
      have hz : ∀ j, raw24096 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24096step0 = (fun i j => raw24096 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24096step0 raw24096; decide +kernel
      have hl : raw24096step0Labels = raw24096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24096 raw24096Labels permutation265 hz
    mixedMoment B raw24096step0 raw24096step0Labels = mixedMoment B raw24096step1 raw24096step1Labels := by
      have ha : raw24096step1 = (fun i j => raw24096step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24096step1 raw24096step0; decide +kernel
      have hl : raw24096step1Labels = raw24096step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24096step0 raw24096step0Labels permutation34 permutation2
    _ = mixedMoment B node2585 node2585Labels := by rfl

def raw24097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw24097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24097 raw24097Labels = mixedMoment B node2771 node2771Labels := by
  calc
    mixedMoment B raw24097 raw24097Labels = mixedMoment B raw24097step0 raw24097step0Labels := by
      have hz : ∀ j, raw24097 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24097step0 = (fun i j => raw24097 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24097step0 raw24097; decide +kernel
      have hl : raw24097step0Labels = raw24097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24097 raw24097Labels permutation346 hz
    mixedMoment B raw24097step0 raw24097step0Labels = mixedMoment B raw24097step1 raw24097step1Labels := by
      have hz : ∀ j, raw24097step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24097step1 = (fun i j => raw24097step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24097step1 raw24097step0; decide +kernel
      have hl : raw24097step1Labels = raw24097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24097step0 raw24097step0Labels permutation56 hz
    _ = mixedMoment B node2771 node2771Labels := by rfl

def raw24098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, -2, 2], ![2, 0, -2]]
def raw24098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -2, 2], ![2, 0, -2]]
def raw24098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -2, 2], ![2, 0, -2]]
def raw24098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24098step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24098 raw24098Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw24098 raw24098Labels = mixedMoment B raw24098step0 raw24098step0Labels := by
      have hz : ∀ j, raw24098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24098step0 = (fun i j => raw24098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24098step0 raw24098; decide +kernel
      have hl : raw24098step0Labels = raw24098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24098 raw24098Labels permutation346 hz
    mixedMoment B raw24098step0 raw24098step0Labels = mixedMoment B raw24098step1 raw24098step1Labels := by
      have hz : ∀ j, raw24098step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24098step1 = (fun i j => raw24098step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24098step1 raw24098step0; decide +kernel
      have hl : raw24098step1Labels = raw24098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24098step0 raw24098step0Labels permutation56 hz
    mixedMoment B raw24098step1 raw24098step1Labels = mixedMoment B raw24098step2 raw24098step2Labels := by
      have ha : raw24098step2 = (fun i j => raw24098step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24098step2 raw24098step1; decide +kernel
      have hl : raw24098step2Labels = raw24098step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24098step1 raw24098step1Labels permutation10 permutation2
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw24099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2], ![1, 1, -2]]
def raw24099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2], ![1, 1, -2]]
def raw24099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -3, 2], ![1, 1, -2]]
def raw24099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24099step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw24099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24099 raw24099Labels = mixedMoment B node2779 node2779Labels := by
  calc
    mixedMoment B raw24099 raw24099Labels = mixedMoment B raw24099step0 raw24099step0Labels := by
      have hz : ∀ j, raw24099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24099step0 = (fun i j => raw24099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24099step0 raw24099; decide +kernel
      have hl : raw24099step0Labels = raw24099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24099 raw24099Labels permutation346 hz
    mixedMoment B raw24099step0 raw24099step0Labels = mixedMoment B raw24099step1 raw24099step1Labels := by
      have hz : ∀ j, raw24099step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24099step1 = (fun i j => raw24099step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24099step1 raw24099step0; decide +kernel
      have hl : raw24099step1Labels = raw24099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24099step0 raw24099step0Labels permutation56 hz
    mixedMoment B raw24099step1 raw24099step1Labels = mixedMoment B raw24099step2 raw24099step2Labels := by
      have ha : raw24099step2 = (fun i j => raw24099step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24099step2 raw24099step1; decide +kernel
      have hl : raw24099step2Labels = raw24099step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24099step1 raw24099step1Labels permutation10 permutation2
    _ = mixedMoment B node2779 node2779Labels := by rfl

def raw24100 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![-2, 2], ![2, -2]]
def raw24100Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24100step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![-2, 2], ![2, -2]]
def raw24100step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24100step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-2, 2], ![2, -2]]
def raw24100step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24100step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw24100step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24100 raw24100Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw24100 raw24100Labels = mixedMoment B raw24100step0 raw24100step0Labels := by
      have hz : ∀ j, raw24100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24100step0 = (fun i j => raw24100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24100step0 raw24100; decide +kernel
      have hl : raw24100step0Labels = raw24100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24100 raw24100Labels permutation346 hz
    mixedMoment B raw24100step0 raw24100step0Labels = mixedMoment B raw24100step1 raw24100step1Labels := by
      have hz : ∀ j, raw24100step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24100step1 = (fun i j => raw24100step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24100step1 raw24100step0; decide +kernel
      have hl : raw24100step1Labels = raw24100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24100step0 raw24100step0Labels permutation56 hz
    mixedMoment B raw24100step1 raw24100step1Labels = mixedMoment B raw24100step2 raw24100step2Labels := by
      have ha : raw24100step2 = (fun i j => raw24100step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24100step2 raw24100step1; decide +kernel
      have hl : raw24100step2Labels = raw24100step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24100step1 raw24100step1Labels permutation10 permutation0
    _ = mixedMoment B node4089 node4089Labels := by rfl

def raw24101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24101step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24101 raw24101Labels = mixedMoment B node4182 node4182Labels := by
  calc
    mixedMoment B raw24101 raw24101Labels = mixedMoment B raw24101step0 raw24101step0Labels := by
      have hz : ∀ j, raw24101 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24101step0 = (fun i j => raw24101 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24101step0 raw24101; decide +kernel
      have hl : raw24101step0Labels = raw24101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24101 raw24101Labels permutation346 hz
    mixedMoment B raw24101step0 raw24101step0Labels = mixedMoment B raw24101step1 raw24101step1Labels := by
      have ha : raw24101step1 = (fun i j => raw24101step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24101step1 raw24101step0; decide +kernel
      have hl : raw24101step1Labels = raw24101step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24101step0 raw24101step0Labels permutation32 permutation3
    mixedMoment B raw24101step1 raw24101step1Labels = mixedMoment B raw24101step2 raw24101step2Labels := by
      have ha : raw24101step2 = raw24101step1 := by apply Matrix.ext; unfold raw24101step2 raw24101step1; decide +kernel
      have hl : raw24101step1Labels = labelEmbedding6 ∘ raw24101step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24101step1 raw24101step1Labels raw24101step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4182 node4182Labels := by rfl

def raw24102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24102step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24102 raw24102Labels = mixedMoment B node4550 node4550Labels := by
  calc
    mixedMoment B raw24102 raw24102Labels = mixedMoment B raw24102step0 raw24102step0Labels := by
      have ha : raw24102step0 = (fun i j => raw24102 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24102step0 raw24102; decide +kernel
      have hl : raw24102step0Labels = raw24102Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24102 raw24102Labels permutation176 permutation3
    mixedMoment B raw24102step0 raw24102step0Labels = mixedMoment B raw24102step1 raw24102step1Labels := by
      have ha : raw24102step1 = raw24102step0 := by apply Matrix.ext; unfold raw24102step1 raw24102step0; decide +kernel
      have hl : raw24102step0Labels = labelEmbedding6 ∘ raw24102step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24102step0 raw24102step0Labels raw24102step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4550 node4550Labels := by rfl

def raw24103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24103 raw24103Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw24103 raw24103Labels = mixedMoment B raw24103step0 raw24103step0Labels := by
      have hz : ∀ j, raw24103 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24103step0 = (fun i j => raw24103 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24103step0 raw24103; decide +kernel
      have hl : raw24103step0Labels = raw24103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24103 raw24103Labels permutation520 hz
    mixedMoment B raw24103step0 raw24103step0Labels = mixedMoment B raw24103step1 raw24103step1Labels := by
      have hz : ∀ j, raw24103step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw24103step1 = (fun i j => raw24103step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw24103step1 raw24103step0; decide +kernel
      have hl : raw24103step1Labels = raw24103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24103step0 raw24103step0Labels permutation80 hz
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw24104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24104step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24104 raw24104Labels = mixedMoment B node4182 node4182Labels := by
  calc
    mixedMoment B raw24104 raw24104Labels = mixedMoment B raw24104step0 raw24104step0Labels := by
      have hz : ∀ j, raw24104 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24104step0 = (fun i j => raw24104 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24104step0 raw24104; decide +kernel
      have hl : raw24104step0Labels = raw24104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24104 raw24104Labels permutation265 hz
    mixedMoment B raw24104step0 raw24104step0Labels = mixedMoment B raw24104step1 raw24104step1Labels := by
      have ha : raw24104step1 = (fun i j => raw24104step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24104step1 raw24104step0; decide +kernel
      have hl : raw24104step1Labels = raw24104step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24104step0 raw24104step0Labels permutation32 permutation3
    mixedMoment B raw24104step1 raw24104step1Labels = mixedMoment B raw24104step2 raw24104step2Labels := by
      have ha : raw24104step2 = raw24104step1 := by apply Matrix.ext; unfold raw24104step2 raw24104step1; decide +kernel
      have hl : raw24104step1Labels = labelEmbedding6 ∘ raw24104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24104step1 raw24104step1Labels raw24104step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4182 node4182Labels := by rfl

def raw24105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24105step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24105 raw24105Labels = mixedMoment B node4550 node4550Labels := by
  calc
    mixedMoment B raw24105 raw24105Labels = mixedMoment B raw24105step0 raw24105step0Labels := by
      have ha : raw24105step0 = (fun i j => raw24105 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24105step0 raw24105; decide +kernel
      have hl : raw24105step0Labels = raw24105Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24105 raw24105Labels permutation152 permutation3
    mixedMoment B raw24105step0 raw24105step0Labels = mixedMoment B raw24105step1 raw24105step1Labels := by
      have ha : raw24105step1 = raw24105step0 := by apply Matrix.ext; unfold raw24105step1 raw24105step0; decide +kernel
      have hl : raw24105step0Labels = labelEmbedding6 ∘ raw24105step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24105step0 raw24105step0Labels raw24105step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4550 node4550Labels := by rfl

def raw24106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24106step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24106 raw24106Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw24106 raw24106Labels = mixedMoment B raw24106step0 raw24106step0Labels := by
      have hz : ∀ j, raw24106 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24106step0 = (fun i j => raw24106 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24106step0 raw24106; decide +kernel
      have hl : raw24106step0Labels = raw24106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24106 raw24106Labels permutation520 hz
    mixedMoment B raw24106step0 raw24106step0Labels = mixedMoment B raw24106step1 raw24106step1Labels := by
      have hz : ∀ j, raw24106step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24106step1 = (fun i j => raw24106step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24106step1 raw24106step0; decide +kernel
      have hl : raw24106step1Labels = raw24106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24106step0 raw24106step0Labels permutation56 hz
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw24107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24107step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24107step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24107step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24107step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24107 raw24107Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw24107 raw24107Labels = mixedMoment B raw24107step0 raw24107step0Labels := by
      have hz : ∀ j, raw24107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24107step0 = (fun i j => raw24107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24107step0 raw24107; decide +kernel
      have hl : raw24107step0Labels = raw24107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24107 raw24107Labels permutation346 hz
    mixedMoment B raw24107step0 raw24107step0Labels = mixedMoment B raw24107step1 raw24107step1Labels := by
      have hz : ∀ j, raw24107step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24107step1 = (fun i j => raw24107step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24107step1 raw24107step0; decide +kernel
      have hl : raw24107step1Labels = raw24107step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24107step0 raw24107step0Labels permutation56 hz
    mixedMoment B raw24107step1 raw24107step1Labels = mixedMoment B raw24107step2 raw24107step2Labels := by
      have ha : raw24107step2 = (fun i j => raw24107step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24107step2 raw24107step1; decide +kernel
      have hl : raw24107step2Labels = raw24107step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24107step1 raw24107step1Labels permutation11 permutation3
    mixedMoment B raw24107step2 raw24107step2Labels = mixedMoment B raw24107step3 raw24107step3Labels := by
      have ha : raw24107step3 = raw24107step2 := by apply Matrix.ext; unfold raw24107step3 raw24107step2; decide +kernel
      have hl : raw24107step2Labels = labelEmbedding6 ∘ raw24107step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24107step2 raw24107step2Labels raw24107step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4185 node4185Labels := by rfl

def raw24108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24108step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24108 raw24108Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw24108 raw24108Labels = mixedMoment B raw24108step0 raw24108step0Labels := by
      have hz : ∀ j, raw24108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24108step0 = (fun i j => raw24108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24108step0 raw24108; decide +kernel
      have hl : raw24108step0Labels = raw24108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24108 raw24108Labels permutation346 hz
    mixedMoment B raw24108step0 raw24108step0Labels = mixedMoment B raw24108step1 raw24108step1Labels := by
      have ha : raw24108step1 = (fun i j => raw24108step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24108step1 raw24108step0; decide +kernel
      have hl : raw24108step1Labels = raw24108step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24108step0 raw24108step0Labels permutation35 permutation3
    mixedMoment B raw24108step1 raw24108step1Labels = mixedMoment B raw24108step2 raw24108step2Labels := by
      have ha : raw24108step2 = raw24108step1 := by apply Matrix.ext; unfold raw24108step2 raw24108step1; decide +kernel
      have hl : raw24108step1Labels = labelEmbedding6 ∘ raw24108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24108step1 raw24108step1Labels raw24108step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw24109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24109step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24109 raw24109Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw24109 raw24109Labels = mixedMoment B raw24109step0 raw24109step0Labels := by
      have hz : ∀ j, raw24109 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24109step0 = (fun i j => raw24109 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24109step0 raw24109; decide +kernel
      have hl : raw24109step0Labels = raw24109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24109 raw24109Labels permutation265 hz
    mixedMoment B raw24109step0 raw24109step0Labels = mixedMoment B raw24109step1 raw24109step1Labels := by
      have ha : raw24109step1 = (fun i j => raw24109step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24109step1 raw24109step0; decide +kernel
      have hl : raw24109step1Labels = raw24109step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24109step0 raw24109step0Labels permutation35 permutation3
    mixedMoment B raw24109step1 raw24109step1Labels = mixedMoment B raw24109step2 raw24109step2Labels := by
      have ha : raw24109step2 = raw24109step1 := by apply Matrix.ext; unfold raw24109step2 raw24109step1; decide +kernel
      have hl : raw24109step1Labels = labelEmbedding6 ∘ raw24109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24109step1 raw24109step1Labels raw24109step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw24110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24110step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw24110step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24110 raw24110Labels = mixedMoment B node4627 node4627Labels := by
  calc
    mixedMoment B raw24110 raw24110Labels = mixedMoment B raw24110step0 raw24110step0Labels := by
      have hz : ∀ j, raw24110 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24110step0 = (fun i j => raw24110 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24110step0 raw24110; decide +kernel
      have hl : raw24110step0Labels = raw24110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24110 raw24110Labels permutation520 hz
    mixedMoment B raw24110step0 raw24110step0Labels = mixedMoment B raw24110step1 raw24110step1Labels := by
      have hz : ∀ j, raw24110step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw24110step1 = (fun i j => raw24110step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw24110step1 raw24110step0; decide +kernel
      have hl : raw24110step1Labels = raw24110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24110step0 raw24110step0Labels permutation80 hz
    mixedMoment B raw24110step1 raw24110step1Labels = mixedMoment B raw24110step2 raw24110step2Labels := by
      have hz : ∀ j, raw24110step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw24110step2 = (fun i j => raw24110step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw24110step2 raw24110step1; decide +kernel
      have hl : raw24110step2Labels = raw24110step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24110step1 raw24110step1Labels permutation14 hz
    _ = mixedMoment B node4627 node4627Labels := by rfl

def raw24111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24111step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24111 raw24111Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw24111 raw24111Labels = mixedMoment B raw24111step0 raw24111step0Labels := by
      have hz : ∀ j, raw24111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24111step0 = (fun i j => raw24111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24111step0 raw24111; decide +kernel
      have hl : raw24111step0Labels = raw24111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24111 raw24111Labels permutation346 hz
    mixedMoment B raw24111step0 raw24111step0Labels = mixedMoment B raw24111step1 raw24111step1Labels := by
      have hz : ∀ j, raw24111step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24111step1 = (fun i j => raw24111step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24111step1 raw24111step0; decide +kernel
      have hl : raw24111step1Labels = raw24111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24111step0 raw24111step0Labels permutation56 hz
    mixedMoment B raw24111step1 raw24111step1Labels = mixedMoment B raw24111step2 raw24111step2Labels := by
      have ha : raw24111step2 = (fun i j => raw24111step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24111step2 raw24111step1; decide +kernel
      have hl : raw24111step2Labels = raw24111step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24111step1 raw24111step1Labels permutation12 permutation3
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw24112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24112 raw24112Labels = mixedMoment B node610 node610Labels := by
  calc
    mixedMoment B raw24112 raw24112Labels = mixedMoment B raw24112step0 raw24112step0Labels := by
      have hz : ∀ j, raw24112 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24112step0 = (fun i j => raw24112 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24112step0 raw24112; decide +kernel
      have hl : raw24112step0Labels = raw24112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24112 raw24112Labels permutation346 hz
    mixedMoment B raw24112step0 raw24112step0Labels = mixedMoment B raw24112step1 raw24112step1Labels := by
      have ha : raw24112step1 = (fun i j => raw24112step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24112step1 raw24112step0; decide +kernel
      have hl : raw24112step1Labels = raw24112step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24112step0 raw24112step0Labels permutation32 permutation3
    _ = mixedMoment B node610 node610Labels := by rfl

def raw24113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24113 raw24113Labels = mixedMoment B node1135 node1135Labels := by
  calc
    mixedMoment B raw24113 raw24113Labels = mixedMoment B raw24113step0 raw24113step0Labels := by
      have ha : raw24113step0 = (fun i j => raw24113 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24113step0 raw24113; decide +kernel
      have hl : raw24113step0Labels = raw24113Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24113 raw24113Labels permutation176 permutation3
    _ = mixedMoment B node1135 node1135Labels := by rfl

def raw24114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24114step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24114 raw24114Labels = mixedMoment B node1305 node1305Labels := by
  calc
    mixedMoment B raw24114 raw24114Labels = mixedMoment B raw24114step0 raw24114step0Labels := by
      have hz : ∀ j, raw24114 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24114step0 = (fun i j => raw24114 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24114step0 raw24114; decide +kernel
      have hl : raw24114step0Labels = raw24114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24114 raw24114Labels permutation520 hz
    mixedMoment B raw24114step0 raw24114step0Labels = mixedMoment B raw24114step1 raw24114step1Labels := by
      have hz : ∀ j, raw24114step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw24114step1 = (fun i j => raw24114step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw24114step1 raw24114step0; decide +kernel
      have hl : raw24114step1Labels = raw24114step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24114step0 raw24114step0Labels permutation80 hz
    mixedMoment B raw24114step1 raw24114step1Labels = mixedMoment B raw24114step2 raw24114step2Labels := by
      have ha : raw24114step2 = (fun i j => raw24114step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24114step2 raw24114step1; decide +kernel
      have hl : raw24114step2Labels = raw24114step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24114step1 raw24114step1Labels permutation8 permutation3
    _ = mixedMoment B node1305 node1305Labels := by rfl

def raw24115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24115 raw24115Labels = mixedMoment B node610 node610Labels := by
  calc
    mixedMoment B raw24115 raw24115Labels = mixedMoment B raw24115step0 raw24115step0Labels := by
      have hz : ∀ j, raw24115 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24115step0 = (fun i j => raw24115 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24115step0 raw24115; decide +kernel
      have hl : raw24115step0Labels = raw24115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24115 raw24115Labels permutation265 hz
    mixedMoment B raw24115step0 raw24115step0Labels = mixedMoment B raw24115step1 raw24115step1Labels := by
      have ha : raw24115step1 = (fun i j => raw24115step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24115step1 raw24115step0; decide +kernel
      have hl : raw24115step1Labels = raw24115step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24115step0 raw24115step0Labels permutation32 permutation3
    _ = mixedMoment B node610 node610Labels := by rfl

def raw24116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24116 raw24116Labels = mixedMoment B node1135 node1135Labels := by
  calc
    mixedMoment B raw24116 raw24116Labels = mixedMoment B raw24116step0 raw24116step0Labels := by
      have ha : raw24116step0 = (fun i j => raw24116 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24116step0 raw24116; decide +kernel
      have hl : raw24116step0Labels = raw24116Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24116 raw24116Labels permutation152 permutation3
    _ = mixedMoment B node1135 node1135Labels := by rfl

def raw24117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24117step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24117step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24117 raw24117Labels = mixedMoment B node1305 node1305Labels := by
  calc
    mixedMoment B raw24117 raw24117Labels = mixedMoment B raw24117step0 raw24117step0Labels := by
      have hz : ∀ j, raw24117 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24117step0 = (fun i j => raw24117 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24117step0 raw24117; decide +kernel
      have hl : raw24117step0Labels = raw24117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24117 raw24117Labels permutation520 hz
    mixedMoment B raw24117step0 raw24117step0Labels = mixedMoment B raw24117step1 raw24117step1Labels := by
      have hz : ∀ j, raw24117step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24117step1 = (fun i j => raw24117step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24117step1 raw24117step0; decide +kernel
      have hl : raw24117step1Labels = raw24117step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24117step0 raw24117step0Labels permutation56 hz
    mixedMoment B raw24117step1 raw24117step1Labels = mixedMoment B raw24117step2 raw24117step2Labels := by
      have ha : raw24117step2 = (fun i j => raw24117step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24117step2 raw24117step1; decide +kernel
      have hl : raw24117step2Labels = raw24117step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24117step1 raw24117step1Labels permutation8 permutation3
    _ = mixedMoment B node1305 node1305Labels := by rfl

def raw24118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24118step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24118 raw24118Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw24118 raw24118Labels = mixedMoment B raw24118step0 raw24118step0Labels := by
      have hz : ∀ j, raw24118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24118step0 = (fun i j => raw24118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24118step0 raw24118; decide +kernel
      have hl : raw24118step0Labels = raw24118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24118 raw24118Labels permutation346 hz
    mixedMoment B raw24118step0 raw24118step0Labels = mixedMoment B raw24118step1 raw24118step1Labels := by
      have hz : ∀ j, raw24118step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24118step1 = (fun i j => raw24118step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24118step1 raw24118step0; decide +kernel
      have hl : raw24118step1Labels = raw24118step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24118step0 raw24118step0Labels permutation56 hz
    mixedMoment B raw24118step1 raw24118step1Labels = mixedMoment B raw24118step2 raw24118step2Labels := by
      have ha : raw24118step2 = (fun i j => raw24118step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24118step2 raw24118step1; decide +kernel
      have hl : raw24118step2Labels = raw24118step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24118step1 raw24118step1Labels permutation11 permutation3
    _ = mixedMoment B node613 node613Labels := by rfl

def raw24119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24119 raw24119Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw24119 raw24119Labels = mixedMoment B raw24119step0 raw24119step0Labels := by
      have hz : ∀ j, raw24119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24119step0 = (fun i j => raw24119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24119step0 raw24119; decide +kernel
      have hl : raw24119step0Labels = raw24119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24119 raw24119Labels permutation346 hz
    mixedMoment B raw24119step0 raw24119step0Labels = mixedMoment B raw24119step1 raw24119step1Labels := by
      have ha : raw24119step1 = (fun i j => raw24119step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24119step1 raw24119step0; decide +kernel
      have hl : raw24119step1Labels = raw24119step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24119step0 raw24119step0Labels permutation35 permutation3
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw24120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24120step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24120 raw24120Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw24120 raw24120Labels = mixedMoment B raw24120step0 raw24120step0Labels := by
      have hz : ∀ j, raw24120 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24120step0 = (fun i j => raw24120 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24120step0 raw24120; decide +kernel
      have hl : raw24120step0Labels = raw24120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24120 raw24120Labels permutation265 hz
    mixedMoment B raw24120step0 raw24120step0Labels = mixedMoment B raw24120step1 raw24120step1Labels := by
      have ha : raw24120step1 = (fun i j => raw24120step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24120step1 raw24120step0; decide +kernel
      have hl : raw24120step1Labels = raw24120step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24120step0 raw24120step0Labels permutation35 permutation3
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw24121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24121step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24121step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw24121step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24121step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw24121step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24121 raw24121Labels = mixedMoment B node1311 node1311Labels := by
  calc
    mixedMoment B raw24121 raw24121Labels = mixedMoment B raw24121step0 raw24121step0Labels := by
      have hz : ∀ j, raw24121 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24121step0 = (fun i j => raw24121 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24121step0 raw24121; decide +kernel
      have hl : raw24121step0Labels = raw24121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24121 raw24121Labels permutation520 hz
    mixedMoment B raw24121step0 raw24121step0Labels = mixedMoment B raw24121step1 raw24121step1Labels := by
      have hz : ∀ j, raw24121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw24121step1 = (fun i j => raw24121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw24121step1 raw24121step0; decide +kernel
      have hl : raw24121step1Labels = raw24121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24121step0 raw24121step0Labels permutation80 hz
    mixedMoment B raw24121step1 raw24121step1Labels = mixedMoment B raw24121step2 raw24121step2Labels := by
      have hz : ∀ j, raw24121step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw24121step2 = (fun i j => raw24121step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw24121step2 raw24121step1; decide +kernel
      have hl : raw24121step2Labels = raw24121step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24121step1 raw24121step1Labels permutation14 hz
    mixedMoment B raw24121step2 raw24121step2Labels = mixedMoment B raw24121step3 raw24121step3Labels := by
      have ha : raw24121step3 = (fun i j => raw24121step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24121step3 raw24121step2; decide +kernel
      have hl : raw24121step3Labels = raw24121step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24121step2 raw24121step2Labels permutation3 permutation3
    _ = mixedMoment B node1311 node1311Labels := by rfl

def raw24122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24122step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24122 raw24122Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw24122 raw24122Labels = mixedMoment B raw24122step0 raw24122step0Labels := by
      have hz : ∀ j, raw24122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24122step0 = (fun i j => raw24122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24122step0 raw24122; decide +kernel
      have hl : raw24122step0Labels = raw24122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24122 raw24122Labels permutation346 hz
    mixedMoment B raw24122step0 raw24122step0Labels = mixedMoment B raw24122step1 raw24122step1Labels := by
      have ha : raw24122step1 = (fun i j => raw24122step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24122step1 raw24122step0; decide +kernel
      have hl : raw24122step1Labels = raw24122step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24122step0 raw24122step0Labels permutation40 permutation3
    mixedMoment B raw24122step1 raw24122step1Labels = mixedMoment B raw24122step2 raw24122step2Labels := by
      have ha : raw24122step2 = raw24122step1 := by apply Matrix.ext; unfold raw24122step2 raw24122step1; decide +kernel
      have hl : raw24122step1Labels = labelEmbedding6 ∘ raw24122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24122step1 raw24122step1Labels raw24122step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4172 node4172Labels := by rfl

def raw24123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24123step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24123 raw24123Labels = mixedMoment B node4541 node4541Labels := by
  calc
    mixedMoment B raw24123 raw24123Labels = mixedMoment B raw24123step0 raw24123step0Labels := by
      have ha : raw24123step0 = (fun i j => raw24123 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24123step0 raw24123; decide +kernel
      have hl : raw24123step0Labels = raw24123Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24123 raw24123Labels permutation184 permutation3
    mixedMoment B raw24123step0 raw24123step0Labels = mixedMoment B raw24123step1 raw24123step1Labels := by
      have ha : raw24123step1 = raw24123step0 := by apply Matrix.ext; unfold raw24123step1 raw24123step0; decide +kernel
      have hl : raw24123step0Labels = labelEmbedding6 ∘ raw24123step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24123step0 raw24123step0Labels raw24123step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4541 node4541Labels := by rfl

def raw24124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24124 raw24124Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24124 raw24124Labels = mixedMoment B raw24124step0 raw24124step0Labels := by
      have hz : ∀ j, raw24124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24124step0 = (fun i j => raw24124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24124step0 raw24124; decide +kernel
      have hl : raw24124step0Labels = raw24124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24124 raw24124Labels permutation346 hz
    mixedMoment B raw24124step0 raw24124step0Labels = mixedMoment B raw24124step1 raw24124step1Labels := by
      have ha : raw24124step1 = (fun i j => raw24124step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24124step1 raw24124step0; decide +kernel
      have hl : raw24124step1Labels = raw24124step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24124step0 raw24124step0Labels permutation46 permutation3
    mixedMoment B raw24124step1 raw24124step1Labels = mixedMoment B raw24124step2 raw24124step2Labels := by
      have ha : raw24124step2 = raw24124step1 := by apply Matrix.ext; unfold raw24124step2 raw24124step1; decide +kernel
      have hl : raw24124step1Labels = labelEmbedding6 ∘ raw24124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24124step1 raw24124step1Labels raw24124step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24125step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24125 raw24125Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw24125 raw24125Labels = mixedMoment B raw24125step0 raw24125step0Labels := by
      have hz : ∀ j, raw24125 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24125step0 = (fun i j => raw24125 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24125step0 raw24125; decide +kernel
      have hl : raw24125step0Labels = raw24125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24125 raw24125Labels permutation265 hz
    mixedMoment B raw24125step0 raw24125step0Labels = mixedMoment B raw24125step1 raw24125step1Labels := by
      have ha : raw24125step1 = (fun i j => raw24125step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24125step1 raw24125step0; decide +kernel
      have hl : raw24125step1Labels = raw24125step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24125step0 raw24125step0Labels permutation40 permutation3
    mixedMoment B raw24125step1 raw24125step1Labels = mixedMoment B raw24125step2 raw24125step2Labels := by
      have ha : raw24125step2 = raw24125step1 := by apply Matrix.ext; unfold raw24125step2 raw24125step1; decide +kernel
      have hl : raw24125step1Labels = labelEmbedding6 ∘ raw24125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24125step1 raw24125step1Labels raw24125step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4172 node4172Labels := by rfl

def raw24126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24126step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24126 raw24126Labels = mixedMoment B node4541 node4541Labels := by
  calc
    mixedMoment B raw24126 raw24126Labels = mixedMoment B raw24126step0 raw24126step0Labels := by
      have ha : raw24126step0 = (fun i j => raw24126 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24126step0 raw24126; decide +kernel
      have hl : raw24126step0Labels = raw24126Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24126 raw24126Labels permutation160 permutation3
    mixedMoment B raw24126step0 raw24126step0Labels = mixedMoment B raw24126step1 raw24126step1Labels := by
      have ha : raw24126step1 = raw24126step0 := by apply Matrix.ext; unfold raw24126step1 raw24126step0; decide +kernel
      have hl : raw24126step0Labels = labelEmbedding6 ∘ raw24126step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24126step0 raw24126step0Labels raw24126step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4541 node4541Labels := by rfl

def raw24127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24127step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24127 raw24127Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24127 raw24127Labels = mixedMoment B raw24127step0 raw24127step0Labels := by
      have hz : ∀ j, raw24127 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24127step0 = (fun i j => raw24127 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24127step0 raw24127; decide +kernel
      have hl : raw24127step0Labels = raw24127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24127 raw24127Labels permutation265 hz
    mixedMoment B raw24127step0 raw24127step0Labels = mixedMoment B raw24127step1 raw24127step1Labels := by
      have ha : raw24127step1 = (fun i j => raw24127step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24127step1 raw24127step0; decide +kernel
      have hl : raw24127step1Labels = raw24127step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24127step0 raw24127step0Labels permutation46 permutation3
    mixedMoment B raw24127step1 raw24127step1Labels = mixedMoment B raw24127step2 raw24127step2Labels := by
      have ha : raw24127step2 = raw24127step1 := by apply Matrix.ext; unfold raw24127step2 raw24127step1; decide +kernel
      have hl : raw24127step1Labels = labelEmbedding6 ∘ raw24127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24127step1 raw24127step1Labels raw24127step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24128step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24128 raw24128Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw24128 raw24128Labels = mixedMoment B raw24128step0 raw24128step0Labels := by
      have hz : ∀ j, raw24128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24128step0 = (fun i j => raw24128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24128step0 raw24128; decide +kernel
      have hl : raw24128step0Labels = raw24128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24128 raw24128Labels permutation346 hz
    mixedMoment B raw24128step0 raw24128step0Labels = mixedMoment B raw24128step1 raw24128step1Labels := by
      have hz : ∀ j, raw24128step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24128step1 = (fun i j => raw24128step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24128step1 raw24128step0; decide +kernel
      have hl : raw24128step1Labels = raw24128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24128step0 raw24128step0Labels permutation56 hz
    mixedMoment B raw24128step1 raw24128step1Labels = mixedMoment B raw24128step2 raw24128step2Labels := by
      have ha : raw24128step2 = (fun i j => raw24128step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24128step2 raw24128step1; decide +kernel
      have hl : raw24128step2Labels = raw24128step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24128step1 raw24128step1Labels permutation10 permutation3
    mixedMoment B raw24128step2 raw24128step2Labels = mixedMoment B raw24128step3 raw24128step3Labels := by
      have ha : raw24128step3 = raw24128step2 := by apply Matrix.ext; unfold raw24128step3 raw24128step2; decide +kernel
      have hl : raw24128step2Labels = labelEmbedding6 ∘ raw24128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24128step2 raw24128step2Labels raw24128step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4180 node4180Labels := by rfl

def raw24129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24129step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24129 raw24129Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw24129 raw24129Labels = mixedMoment B raw24129step0 raw24129step0Labels := by
      have hz : ∀ j, raw24129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24129step0 = (fun i j => raw24129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24129step0 raw24129; decide +kernel
      have hl : raw24129step0Labels = raw24129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24129 raw24129Labels permutation346 hz
    mixedMoment B raw24129step0 raw24129step0Labels = mixedMoment B raw24129step1 raw24129step1Labels := by
      have ha : raw24129step1 = (fun i j => raw24129step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24129step1 raw24129step0; decide +kernel
      have hl : raw24129step1Labels = raw24129step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24129step0 raw24129step0Labels permutation34 permutation3
    mixedMoment B raw24129step1 raw24129step1Labels = mixedMoment B raw24129step2 raw24129step2Labels := by
      have ha : raw24129step2 = raw24129step1 := by apply Matrix.ext; unfold raw24129step2 raw24129step1; decide +kernel
      have hl : raw24129step1Labels = labelEmbedding6 ∘ raw24129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24129step1 raw24129step1Labels raw24129step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw24130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24130step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24130step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24130 raw24130Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw24130 raw24130Labels = mixedMoment B raw24130step0 raw24130step0Labels := by
      have hz : ∀ j, raw24130 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24130step0 = (fun i j => raw24130 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24130step0 raw24130; decide +kernel
      have hl : raw24130step0Labels = raw24130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24130 raw24130Labels permutation265 hz
    mixedMoment B raw24130step0 raw24130step0Labels = mixedMoment B raw24130step1 raw24130step1Labels := by
      have ha : raw24130step1 = (fun i j => raw24130step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24130step1 raw24130step0; decide +kernel
      have hl : raw24130step1Labels = raw24130step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24130step0 raw24130step0Labels permutation34 permutation3
    mixedMoment B raw24130step1 raw24130step1Labels = mixedMoment B raw24130step2 raw24130step2Labels := by
      have ha : raw24130step2 = raw24130step1 := by apply Matrix.ext; unfold raw24130step2 raw24130step1; decide +kernel
      have hl : raw24130step1Labels = labelEmbedding6 ∘ raw24130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24130step1 raw24130step1Labels raw24130step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw24131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24131step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24131step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24131step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24131 raw24131Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw24131 raw24131Labels = mixedMoment B raw24131step0 raw24131step0Labels := by
      have hz : ∀ j, raw24131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24131step0 = (fun i j => raw24131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24131step0 raw24131; decide +kernel
      have hl : raw24131step0Labels = raw24131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24131 raw24131Labels permutation346 hz
    mixedMoment B raw24131step0 raw24131step0Labels = mixedMoment B raw24131step1 raw24131step1Labels := by
      have hz : ∀ j, raw24131step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24131step1 = (fun i j => raw24131step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24131step1 raw24131step0; decide +kernel
      have hl : raw24131step1Labels = raw24131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24131step0 raw24131step0Labels permutation56 hz
    mixedMoment B raw24131step1 raw24131step1Labels = mixedMoment B raw24131step2 raw24131step2Labels := by
      have ha : raw24131step2 = (fun i j => raw24131step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24131step2 raw24131step1; decide +kernel
      have hl : raw24131step2Labels = raw24131step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24131step1 raw24131step1Labels permutation10 permutation3
    mixedMoment B raw24131step2 raw24131step2Labels = mixedMoment B raw24131step3 raw24131step3Labels := by
      have ha : raw24131step3 = raw24131step2 := by apply Matrix.ext; unfold raw24131step3 raw24131step2; decide +kernel
      have hl : raw24131step2Labels = labelEmbedding6 ∘ raw24131step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24131step2 raw24131step2Labels raw24131step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw24132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24132step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24132step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24132 raw24132Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw24132 raw24132Labels = mixedMoment B raw24132step0 raw24132step0Labels := by
      have hz : ∀ j, raw24132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24132step0 = (fun i j => raw24132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24132step0 raw24132; decide +kernel
      have hl : raw24132step0Labels = raw24132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24132 raw24132Labels permutation346 hz
    mixedMoment B raw24132step0 raw24132step0Labels = mixedMoment B raw24132step1 raw24132step1Labels := by
      have hz : ∀ j, raw24132step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24132step1 = (fun i j => raw24132step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24132step1 raw24132step0; decide +kernel
      have hl : raw24132step1Labels = raw24132step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24132step0 raw24132step0Labels permutation56 hz
    mixedMoment B raw24132step1 raw24132step1Labels = mixedMoment B raw24132step2 raw24132step2Labels := by
      have ha : raw24132step2 = (fun i j => raw24132step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24132step2 raw24132step1; decide +kernel
      have hl : raw24132step2Labels = raw24132step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24132step1 raw24132step1Labels permutation8 permutation3
    mixedMoment B raw24132step2 raw24132step2Labels = mixedMoment B raw24132step3 raw24132step3Labels := by
      have ha : raw24132step3 = raw24132step2 := by apply Matrix.ext; unfold raw24132step3 raw24132step2; decide +kernel
      have hl : raw24132step2Labels = labelEmbedding6 ∘ raw24132step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24132step2 raw24132step2Labels raw24132step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4180 node4180Labels := by rfl

def raw24133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24133step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24133step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24133 raw24133Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw24133 raw24133Labels = mixedMoment B raw24133step0 raw24133step0Labels := by
      have hz : ∀ j, raw24133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24133step0 = (fun i j => raw24133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24133step0 raw24133; decide +kernel
      have hl : raw24133step0Labels = raw24133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24133 raw24133Labels permutation346 hz
    mixedMoment B raw24133step0 raw24133step0Labels = mixedMoment B raw24133step1 raw24133step1Labels := by
      have ha : raw24133step1 = (fun i j => raw24133step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24133step1 raw24133step0; decide +kernel
      have hl : raw24133step1Labels = raw24133step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24133step0 raw24133step0Labels permutation32 permutation3
    mixedMoment B raw24133step1 raw24133step1Labels = mixedMoment B raw24133step2 raw24133step2Labels := by
      have ha : raw24133step2 = raw24133step1 := by apply Matrix.ext; unfold raw24133step2 raw24133step1; decide +kernel
      have hl : raw24133step1Labels = labelEmbedding6 ∘ raw24133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24133step1 raw24133step1Labels raw24133step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw24134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24134step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24134 raw24134Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw24134 raw24134Labels = mixedMoment B raw24134step0 raw24134step0Labels := by
      have hz : ∀ j, raw24134 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24134step0 = (fun i j => raw24134 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24134step0 raw24134; decide +kernel
      have hl : raw24134step0Labels = raw24134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24134 raw24134Labels permutation265 hz
    mixedMoment B raw24134step0 raw24134step0Labels = mixedMoment B raw24134step1 raw24134step1Labels := by
      have ha : raw24134step1 = (fun i j => raw24134step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24134step1 raw24134step0; decide +kernel
      have hl : raw24134step1Labels = raw24134step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24134step0 raw24134step0Labels permutation32 permutation3
    mixedMoment B raw24134step1 raw24134step1Labels = mixedMoment B raw24134step2 raw24134step2Labels := by
      have ha : raw24134step2 = raw24134step1 := by apply Matrix.ext; unfold raw24134step2 raw24134step1; decide +kernel
      have hl : raw24134step1Labels = labelEmbedding6 ∘ raw24134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24134step1 raw24134step1Labels raw24134step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw24135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24135Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24135step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24135step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24135 raw24135Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw24135 raw24135Labels = mixedMoment B raw24135step0 raw24135step0Labels := by
      have hz : ∀ j, raw24135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24135step0 = (fun i j => raw24135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24135step0 raw24135; decide +kernel
      have hl : raw24135step0Labels = raw24135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24135 raw24135Labels permutation346 hz
    mixedMoment B raw24135step0 raw24135step0Labels = mixedMoment B raw24135step1 raw24135step1Labels := by
      have ha : raw24135step1 = (fun i j => raw24135step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24135step1 raw24135step0; decide +kernel
      have hl : raw24135step1Labels = raw24135step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24135step0 raw24135step0Labels permutation40 permutation3
    _ = mixedMoment B node600 node600Labels := by rfl

def raw24136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24136Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24136 raw24136Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw24136 raw24136Labels = mixedMoment B raw24136step0 raw24136step0Labels := by
      have ha : raw24136step0 = (fun i j => raw24136 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24136step0 raw24136; decide +kernel
      have hl : raw24136step0Labels = raw24136Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24136 raw24136Labels permutation184 permutation3
    _ = mixedMoment B node1126 node1126Labels := by rfl

def raw24137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24137Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24137step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24137 raw24137Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24137 raw24137Labels = mixedMoment B raw24137step0 raw24137step0Labels := by
      have hz : ∀ j, raw24137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24137step0 = (fun i j => raw24137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24137step0 raw24137; decide +kernel
      have hl : raw24137step0Labels = raw24137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24137 raw24137Labels permutation346 hz
    mixedMoment B raw24137step0 raw24137step0Labels = mixedMoment B raw24137step1 raw24137step1Labels := by
      have ha : raw24137step1 = (fun i j => raw24137step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24137step1 raw24137step0; decide +kernel
      have hl : raw24137step1Labels = raw24137step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24137step0 raw24137step0Labels permutation46 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24138Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24138step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24138 raw24138Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw24138 raw24138Labels = mixedMoment B raw24138step0 raw24138step0Labels := by
      have hz : ∀ j, raw24138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24138step0 = (fun i j => raw24138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24138step0 raw24138; decide +kernel
      have hl : raw24138step0Labels = raw24138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24138 raw24138Labels permutation346 hz
    mixedMoment B raw24138step0 raw24138step0Labels = mixedMoment B raw24138step1 raw24138step1Labels := by
      have ha : raw24138step1 = (fun i j => raw24138step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24138step1 raw24138step0; decide +kernel
      have hl : raw24138step1Labels = raw24138step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24138step0 raw24138step0Labels permutation40 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw24139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24139Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24139step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24139step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24139 raw24139Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw24139 raw24139Labels = mixedMoment B raw24139step0 raw24139step0Labels := by
      have hz : ∀ j, raw24139 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24139step0 = (fun i j => raw24139 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24139step0 raw24139; decide +kernel
      have hl : raw24139step0Labels = raw24139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24139 raw24139Labels permutation265 hz
    mixedMoment B raw24139step0 raw24139step0Labels = mixedMoment B raw24139step1 raw24139step1Labels := by
      have ha : raw24139step1 = (fun i j => raw24139step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24139step1 raw24139step0; decide +kernel
      have hl : raw24139step1Labels = raw24139step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24139step0 raw24139step0Labels permutation40 permutation3
    _ = mixedMoment B node600 node600Labels := by rfl

def raw24140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24140Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24140 raw24140Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw24140 raw24140Labels = mixedMoment B raw24140step0 raw24140step0Labels := by
      have ha : raw24140step0 = (fun i j => raw24140 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24140step0 raw24140; decide +kernel
      have hl : raw24140step0Labels = raw24140Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24140 raw24140Labels permutation160 permutation3
    _ = mixedMoment B node1126 node1126Labels := by rfl

def raw24141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24141Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24141step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24141 raw24141Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24141 raw24141Labels = mixedMoment B raw24141step0 raw24141step0Labels := by
      have hz : ∀ j, raw24141 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24141step0 = (fun i j => raw24141 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24141step0 raw24141; decide +kernel
      have hl : raw24141step0Labels = raw24141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24141 raw24141Labels permutation265 hz
    mixedMoment B raw24141step0 raw24141step0Labels = mixedMoment B raw24141step1 raw24141step1Labels := by
      have ha : raw24141step1 = (fun i j => raw24141step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24141step1 raw24141step0; decide +kernel
      have hl : raw24141step1Labels = raw24141step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24141step0 raw24141step0Labels permutation46 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24142Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24142step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24142step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24142 raw24142Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw24142 raw24142Labels = mixedMoment B raw24142step0 raw24142step0Labels := by
      have hz : ∀ j, raw24142 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24142step0 = (fun i j => raw24142 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24142step0 raw24142; decide +kernel
      have hl : raw24142step0Labels = raw24142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24142 raw24142Labels permutation265 hz
    mixedMoment B raw24142step0 raw24142step0Labels = mixedMoment B raw24142step1 raw24142step1Labels := by
      have ha : raw24142step1 = (fun i j => raw24142step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24142step1 raw24142step0; decide +kernel
      have hl : raw24142step1Labels = raw24142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24142step0 raw24142step0Labels permutation40 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw24143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24143Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24143step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24143step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24143step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24143 raw24143Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw24143 raw24143Labels = mixedMoment B raw24143step0 raw24143step0Labels := by
      have hz : ∀ j, raw24143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24143step0 = (fun i j => raw24143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24143step0 raw24143; decide +kernel
      have hl : raw24143step0Labels = raw24143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24143 raw24143Labels permutation346 hz
    mixedMoment B raw24143step0 raw24143step0Labels = mixedMoment B raw24143step1 raw24143step1Labels := by
      have hz : ∀ j, raw24143step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24143step1 = (fun i j => raw24143step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24143step1 raw24143step0; decide +kernel
      have hl : raw24143step1Labels = raw24143step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24143step0 raw24143step0Labels permutation56 hz
    mixedMoment B raw24143step1 raw24143step1Labels = mixedMoment B raw24143step2 raw24143step2Labels := by
      have ha : raw24143step2 = (fun i j => raw24143step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24143step2 raw24143step1; decide +kernel
      have hl : raw24143step2Labels = raw24143step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24143step1 raw24143step1Labels permutation10 permutation3
    _ = mixedMoment B node608 node608Labels := by rfl

def raw24144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24144Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24144step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24144step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24144 raw24144Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw24144 raw24144Labels = mixedMoment B raw24144step0 raw24144step0Labels := by
      have hz : ∀ j, raw24144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24144step0 = (fun i j => raw24144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24144step0 raw24144; decide +kernel
      have hl : raw24144step0Labels = raw24144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24144 raw24144Labels permutation346 hz
    mixedMoment B raw24144step0 raw24144step0Labels = mixedMoment B raw24144step1 raw24144step1Labels := by
      have ha : raw24144step1 = (fun i j => raw24144step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24144step1 raw24144step0; decide +kernel
      have hl : raw24144step1Labels = raw24144step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24144step0 raw24144step0Labels permutation34 permutation3
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw24145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24145Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24145step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24145step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24145 raw24145Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw24145 raw24145Labels = mixedMoment B raw24145step0 raw24145step0Labels := by
      have hz : ∀ j, raw24145 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24145step0 = (fun i j => raw24145 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24145step0 raw24145; decide +kernel
      have hl : raw24145step0Labels = raw24145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24145 raw24145Labels permutation265 hz
    mixedMoment B raw24145step0 raw24145step0Labels = mixedMoment B raw24145step1 raw24145step1Labels := by
      have ha : raw24145step1 = (fun i j => raw24145step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24145step1 raw24145step0; decide +kernel
      have hl : raw24145step1Labels = raw24145step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24145step0 raw24145step0Labels permutation34 permutation3
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw24146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24146Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24146step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24146step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24146 raw24146Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw24146 raw24146Labels = mixedMoment B raw24146step0 raw24146step0Labels := by
      have hz : ∀ j, raw24146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24146step0 = (fun i j => raw24146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24146step0 raw24146; decide +kernel
      have hl : raw24146step0Labels = raw24146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24146 raw24146Labels permutation346 hz
    mixedMoment B raw24146step0 raw24146step0Labels = mixedMoment B raw24146step1 raw24146step1Labels := by
      have hz : ∀ j, raw24146step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24146step1 = (fun i j => raw24146step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24146step1 raw24146step0; decide +kernel
      have hl : raw24146step1Labels = raw24146step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24146step0 raw24146step0Labels permutation56 hz
    mixedMoment B raw24146step1 raw24146step1Labels = mixedMoment B raw24146step2 raw24146step2Labels := by
      have ha : raw24146step2 = (fun i j => raw24146step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24146step2 raw24146step1; decide +kernel
      have hl : raw24146step2Labels = raw24146step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24146step1 raw24146step1Labels permutation10 permutation3
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw24147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24147Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24147step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24147step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24147 raw24147Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw24147 raw24147Labels = mixedMoment B raw24147step0 raw24147step0Labels := by
      have hz : ∀ j, raw24147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24147step0 = (fun i j => raw24147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24147step0 raw24147; decide +kernel
      have hl : raw24147step0Labels = raw24147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24147 raw24147Labels permutation346 hz
    mixedMoment B raw24147step0 raw24147step0Labels = mixedMoment B raw24147step1 raw24147step1Labels := by
      have hz : ∀ j, raw24147step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24147step1 = (fun i j => raw24147step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24147step1 raw24147step0; decide +kernel
      have hl : raw24147step1Labels = raw24147step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24147step0 raw24147step0Labels permutation56 hz
    mixedMoment B raw24147step1 raw24147step1Labels = mixedMoment B raw24147step2 raw24147step2Labels := by
      have ha : raw24147step2 = (fun i j => raw24147step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24147step2 raw24147step1; decide +kernel
      have hl : raw24147step2Labels = raw24147step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24147step1 raw24147step1Labels permutation11 permutation3
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw24148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24148Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24148step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24148step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24148 raw24148Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw24148 raw24148Labels = mixedMoment B raw24148step0 raw24148step0Labels := by
      have hz : ∀ j, raw24148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24148step0 = (fun i j => raw24148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24148step0 raw24148; decide +kernel
      have hl : raw24148step0Labels = raw24148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24148 raw24148Labels permutation346 hz
    mixedMoment B raw24148step0 raw24148step0Labels = mixedMoment B raw24148step1 raw24148step1Labels := by
      have hz : ∀ j, raw24148step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24148step1 = (fun i j => raw24148step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24148step1 raw24148step0; decide +kernel
      have hl : raw24148step1Labels = raw24148step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24148step0 raw24148step0Labels permutation56 hz
    mixedMoment B raw24148step1 raw24148step1Labels = mixedMoment B raw24148step2 raw24148step2Labels := by
      have ha : raw24148step2 = (fun i j => raw24148step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24148step2 raw24148step1; decide +kernel
      have hl : raw24148step2Labels = raw24148step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24148step1 raw24148step1Labels permutation8 permutation3
    _ = mixedMoment B node608 node608Labels := by rfl

def raw24149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24149step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24149 raw24149Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw24149 raw24149Labels = mixedMoment B raw24149step0 raw24149step0Labels := by
      have hz : ∀ j, raw24149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24149step0 = (fun i j => raw24149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24149step0 raw24149; decide +kernel
      have hl : raw24149step0Labels = raw24149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24149 raw24149Labels permutation346 hz
    mixedMoment B raw24149step0 raw24149step0Labels = mixedMoment B raw24149step1 raw24149step1Labels := by
      have ha : raw24149step1 = (fun i j => raw24149step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24149step1 raw24149step0; decide +kernel
      have hl : raw24149step1Labels = raw24149step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24149step0 raw24149step0Labels permutation32 permutation3
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw24150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24150step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24150step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24150 raw24150Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw24150 raw24150Labels = mixedMoment B raw24150step0 raw24150step0Labels := by
      have hz : ∀ j, raw24150 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24150step0 = (fun i j => raw24150 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24150step0 raw24150; decide +kernel
      have hl : raw24150step0Labels = raw24150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24150 raw24150Labels permutation265 hz
    mixedMoment B raw24150step0 raw24150step0Labels = mixedMoment B raw24150step1 raw24150step1Labels := by
      have ha : raw24150step1 = (fun i j => raw24150step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24150step1 raw24150step0; decide +kernel
      have hl : raw24150step1Labels = raw24150step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24150step0 raw24150step0Labels permutation32 permutation3
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw24151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw24151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw24151step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw24151step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24151step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24151 raw24151Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw24151 raw24151Labels = mixedMoment B raw24151step0 raw24151step0Labels := by
      have hz : ∀ j, raw24151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24151step0 = (fun i j => raw24151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24151step0 raw24151; decide +kernel
      have hl : raw24151step0Labels = raw24151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24151 raw24151Labels permutation346 hz
    mixedMoment B raw24151step0 raw24151step0Labels = mixedMoment B raw24151step1 raw24151step1Labels := by
      have hz : ∀ j, raw24151step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24151step1 = (fun i j => raw24151step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24151step1 raw24151step0; decide +kernel
      have hl : raw24151step1Labels = raw24151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24151step0 raw24151step0Labels permutation56 hz
    mixedMoment B raw24151step1 raw24151step1Labels = mixedMoment B raw24151step2 raw24151step2Labels := by
      have ha : raw24151step2 = (fun i j => raw24151step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24151step2 raw24151step1; decide +kernel
      have hl : raw24151step2Labels = raw24151step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24151step1 raw24151step1Labels permutation9 permutation3
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw24152 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24152step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24152 raw24152Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw24152 raw24152Labels = mixedMoment B raw24152step0 raw24152step0Labels := by
      have hz : ∀ j, raw24152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24152step0 = (fun i j => raw24152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24152step0 raw24152; decide +kernel
      have hl : raw24152step0Labels = raw24152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24152 raw24152Labels permutation346 hz
    mixedMoment B raw24152step0 raw24152step0Labels = mixedMoment B raw24152step1 raw24152step1Labels := by
      have ha : raw24152step1 = (fun i j => raw24152step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24152step1 raw24152step0; decide +kernel
      have hl : raw24152step1Labels = raw24152step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24152step0 raw24152step0Labels permutation32 permutation7
    mixedMoment B raw24152step1 raw24152step1Labels = mixedMoment B raw24152step2 raw24152step2Labels := by
      have ha : raw24152step2 = raw24152step1 := by apply Matrix.ext; unfold raw24152step2 raw24152step1; decide +kernel
      have hl : raw24152step1Labels = labelEmbedding10 ∘ raw24152step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24152step1 raw24152step1Labels raw24152step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw24153 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24153step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24153 raw24153Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw24153 raw24153Labels = mixedMoment B raw24153step0 raw24153step0Labels := by
      have hz : ∀ j, raw24153 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24153step0 = (fun i j => raw24153 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24153step0 raw24153; decide +kernel
      have hl : raw24153step0Labels = raw24153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24153 raw24153Labels permutation265 hz
    mixedMoment B raw24153step0 raw24153step0Labels = mixedMoment B raw24153step1 raw24153step1Labels := by
      have ha : raw24153step1 = (fun i j => raw24153step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24153step1 raw24153step0; decide +kernel
      have hl : raw24153step1Labels = raw24153step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24153step0 raw24153step0Labels permutation32 permutation7
    mixedMoment B raw24153step1 raw24153step1Labels = mixedMoment B raw24153step2 raw24153step2Labels := by
      have ha : raw24153step2 = raw24153step1 := by apply Matrix.ext; unfold raw24153step2 raw24153step1; decide +kernel
      have hl : raw24153step1Labels = labelEmbedding10 ∘ raw24153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24153step1 raw24153step1Labels raw24153step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw24154 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24154step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24154step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24154step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24154step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24154 raw24154Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw24154 raw24154Labels = mixedMoment B raw24154step0 raw24154step0Labels := by
      have hz : ∀ j, raw24154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24154step0 = (fun i j => raw24154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24154step0 raw24154; decide +kernel
      have hl : raw24154step0Labels = raw24154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24154 raw24154Labels permutation346 hz
    mixedMoment B raw24154step0 raw24154step0Labels = mixedMoment B raw24154step1 raw24154step1Labels := by
      have hz : ∀ j, raw24154step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24154step1 = (fun i j => raw24154step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24154step1 raw24154step0; decide +kernel
      have hl : raw24154step1Labels = raw24154step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24154step0 raw24154step0Labels permutation56 hz
    mixedMoment B raw24154step1 raw24154step1Labels = mixedMoment B raw24154step2 raw24154step2Labels := by
      have ha : raw24154step2 = (fun i j => raw24154step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24154step2 raw24154step1; decide +kernel
      have hl : raw24154step2Labels = raw24154step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24154step1 raw24154step1Labels permutation10 permutation7
    mixedMoment B raw24154step2 raw24154step2Labels = mixedMoment B raw24154step3 raw24154step3Labels := by
      have ha : raw24154step3 = raw24154step2 := by apply Matrix.ext; unfold raw24154step3 raw24154step2; decide +kernel
      have hl : raw24154step2Labels = labelEmbedding10 ∘ raw24154step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24154step2 raw24154step2Labels raw24154step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw24155 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24155step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24155step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24155step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24155step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24155 raw24155Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw24155 raw24155Labels = mixedMoment B raw24155step0 raw24155step0Labels := by
      have hz : ∀ j, raw24155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24155step0 = (fun i j => raw24155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24155step0 raw24155; decide +kernel
      have hl : raw24155step0Labels = raw24155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24155 raw24155Labels permutation346 hz
    mixedMoment B raw24155step0 raw24155step0Labels = mixedMoment B raw24155step1 raw24155step1Labels := by
      have hz : ∀ j, raw24155step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24155step1 = (fun i j => raw24155step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24155step1 raw24155step0; decide +kernel
      have hl : raw24155step1Labels = raw24155step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24155step0 raw24155step0Labels permutation56 hz
    mixedMoment B raw24155step1 raw24155step1Labels = mixedMoment B raw24155step2 raw24155step2Labels := by
      have ha : raw24155step2 = (fun i j => raw24155step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24155step2 raw24155step1; decide +kernel
      have hl : raw24155step2Labels = raw24155step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24155step1 raw24155step1Labels permutation8 permutation7
    mixedMoment B raw24155step2 raw24155step2Labels = mixedMoment B raw24155step3 raw24155step3Labels := by
      have ha : raw24155step3 = raw24155step2 := by apply Matrix.ext; unfold raw24155step3 raw24155step2; decide +kernel
      have hl : raw24155step2Labels = labelEmbedding10 ∘ raw24155step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24155step2 raw24155step2Labels raw24155step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw24156 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24156step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24156step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24156step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24156step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24156 raw24156Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw24156 raw24156Labels = mixedMoment B raw24156step0 raw24156step0Labels := by
      have hz : ∀ j, raw24156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24156step0 = (fun i j => raw24156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24156step0 raw24156; decide +kernel
      have hl : raw24156step0Labels = raw24156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24156 raw24156Labels permutation346 hz
    mixedMoment B raw24156step0 raw24156step0Labels = mixedMoment B raw24156step1 raw24156step1Labels := by
      have hz : ∀ j, raw24156step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24156step1 = (fun i j => raw24156step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24156step1 raw24156step0; decide +kernel
      have hl : raw24156step1Labels = raw24156step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24156step0 raw24156step0Labels permutation56 hz
    mixedMoment B raw24156step1 raw24156step1Labels = mixedMoment B raw24156step2 raw24156step2Labels := by
      have ha : raw24156step2 = (fun i j => raw24156step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24156step2 raw24156step1; decide +kernel
      have hl : raw24156step2Labels = raw24156step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24156step1 raw24156step1Labels permutation8 permutation7
    mixedMoment B raw24156step2 raw24156step2Labels = mixedMoment B raw24156step3 raw24156step3Labels := by
      have ha : raw24156step3 = raw24156step2 := by apply Matrix.ext; unfold raw24156step3 raw24156step2; decide +kernel
      have hl : raw24156step2Labels = labelEmbedding10 ∘ raw24156step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24156step2 raw24156step2Labels raw24156step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4502 node4502Labels := by rfl

def raw24157 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24157step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24157 raw24157Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw24157 raw24157Labels = mixedMoment B raw24157step0 raw24157step0Labels := by
      have hz : ∀ j, raw24157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24157step0 = (fun i j => raw24157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24157step0 raw24157; decide +kernel
      have hl : raw24157step0Labels = raw24157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24157 raw24157Labels permutation346 hz
    mixedMoment B raw24157step0 raw24157step0Labels = mixedMoment B raw24157step1 raw24157step1Labels := by
      have ha : raw24157step1 = (fun i j => raw24157step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24157step1 raw24157step0; decide +kernel
      have hl : raw24157step1Labels = raw24157step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24157step0 raw24157step0Labels permutation32 permutation6
    mixedMoment B raw24157step1 raw24157step1Labels = mixedMoment B raw24157step2 raw24157step2Labels := by
      have ha : raw24157step2 = raw24157step1 := by apply Matrix.ext; unfold raw24157step2 raw24157step1; decide +kernel
      have hl : raw24157step1Labels = labelEmbedding9 ∘ raw24157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24157step1 raw24157step1Labels raw24157step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw24158 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24158step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24158 raw24158Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw24158 raw24158Labels = mixedMoment B raw24158step0 raw24158step0Labels := by
      have ha : raw24158step0 = (fun i j => raw24158 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24158step0 raw24158; decide +kernel
      have hl : raw24158step0Labels = raw24158Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24158 raw24158Labels permutation176 permutation6
    mixedMoment B raw24158step0 raw24158step0Labels = mixedMoment B raw24158step1 raw24158step1Labels := by
      have ha : raw24158step1 = raw24158step0 := by apply Matrix.ext; unfold raw24158step1 raw24158step0; decide +kernel
      have hl : raw24158step0Labels = labelEmbedding9 ∘ raw24158step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24158step0 raw24158step0Labels raw24158step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw24159 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24159step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24159step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24159 raw24159Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24159 raw24159Labels = mixedMoment B raw24159step0 raw24159step0Labels := by
      have hz : ∀ j, raw24159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24159step0 = (fun i j => raw24159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24159step0 raw24159; decide +kernel
      have hl : raw24159step0Labels = raw24159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24159 raw24159Labels permutation346 hz
    mixedMoment B raw24159step0 raw24159step0Labels = mixedMoment B raw24159step1 raw24159step1Labels := by
      have ha : raw24159step1 = (fun i j => raw24159step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24159step1 raw24159step0; decide +kernel
      have hl : raw24159step1Labels = raw24159step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24159step0 raw24159step0Labels permutation34 permutation7
    mixedMoment B raw24159step1 raw24159step1Labels = mixedMoment B raw24159step2 raw24159step2Labels := by
      have ha : raw24159step2 = raw24159step1 := by apply Matrix.ext; unfold raw24159step2 raw24159step1; decide +kernel
      have hl : raw24159step1Labels = labelEmbedding10 ∘ raw24159step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24159step1 raw24159step1Labels raw24159step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw24160 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24160step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24160step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24160 raw24160Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24160 raw24160Labels = mixedMoment B raw24160step0 raw24160step0Labels := by
      have hz : ∀ j, raw24160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24160step0 = (fun i j => raw24160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24160step0 raw24160; decide +kernel
      have hl : raw24160step0Labels = raw24160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24160 raw24160Labels permutation346 hz
    mixedMoment B raw24160step0 raw24160step0Labels = mixedMoment B raw24160step1 raw24160step1Labels := by
      have ha : raw24160step1 = (fun i j => raw24160step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24160step1 raw24160step0; decide +kernel
      have hl : raw24160step1Labels = raw24160step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24160step0 raw24160step0Labels permutation32 permutation7
    mixedMoment B raw24160step1 raw24160step1Labels = mixedMoment B raw24160step2 raw24160step2Labels := by
      have ha : raw24160step2 = raw24160step1 := by apply Matrix.ext; unfold raw24160step2 raw24160step1; decide +kernel
      have hl : raw24160step1Labels = labelEmbedding10 ∘ raw24160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24160step1 raw24160step1Labels raw24160step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw24161 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24161step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24161step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24161 raw24161Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw24161 raw24161Labels = mixedMoment B raw24161step0 raw24161step0Labels := by
      have hz : ∀ j, raw24161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24161step0 = (fun i j => raw24161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24161step0 raw24161; decide +kernel
      have hl : raw24161step0Labels = raw24161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24161 raw24161Labels permutation346 hz
    mixedMoment B raw24161step0 raw24161step0Labels = mixedMoment B raw24161step1 raw24161step1Labels := by
      have ha : raw24161step1 = (fun i j => raw24161step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24161step1 raw24161step0; decide +kernel
      have hl : raw24161step1Labels = raw24161step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24161step0 raw24161step0Labels permutation32 permutation7
    mixedMoment B raw24161step1 raw24161step1Labels = mixedMoment B raw24161step2 raw24161step2Labels := by
      have ha : raw24161step2 = raw24161step1 := by apply Matrix.ext; unfold raw24161step2 raw24161step1; decide +kernel
      have hl : raw24161step1Labels = labelEmbedding10 ∘ raw24161step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24161step1 raw24161step1Labels raw24161step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw24162 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24162step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24162step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24162 raw24162Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw24162 raw24162Labels = mixedMoment B raw24162step0 raw24162step0Labels := by
      have hz : ∀ j, raw24162 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24162step0 = (fun i j => raw24162 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24162step0 raw24162; decide +kernel
      have hl : raw24162step0Labels = raw24162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24162 raw24162Labels permutation265 hz
    mixedMoment B raw24162step0 raw24162step0Labels = mixedMoment B raw24162step1 raw24162step1Labels := by
      have ha : raw24162step1 = (fun i j => raw24162step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24162step1 raw24162step0; decide +kernel
      have hl : raw24162step1Labels = raw24162step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24162step0 raw24162step0Labels permutation32 permutation6
    mixedMoment B raw24162step1 raw24162step1Labels = mixedMoment B raw24162step2 raw24162step2Labels := by
      have ha : raw24162step2 = raw24162step1 := by apply Matrix.ext; unfold raw24162step2 raw24162step1; decide +kernel
      have hl : raw24162step1Labels = labelEmbedding9 ∘ raw24162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24162step1 raw24162step1Labels raw24162step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw24163 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24163step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24163 raw24163Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw24163 raw24163Labels = mixedMoment B raw24163step0 raw24163step0Labels := by
      have ha : raw24163step0 = (fun i j => raw24163 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24163step0 raw24163; decide +kernel
      have hl : raw24163step0Labels = raw24163Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24163 raw24163Labels permutation152 permutation6
    mixedMoment B raw24163step0 raw24163step0Labels = mixedMoment B raw24163step1 raw24163step1Labels := by
      have ha : raw24163step1 = raw24163step0 := by apply Matrix.ext; unfold raw24163step1 raw24163step0; decide +kernel
      have hl : raw24163step0Labels = labelEmbedding9 ∘ raw24163step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24163step0 raw24163step0Labels raw24163step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw24164 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24164step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24164step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24164 raw24164Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24164 raw24164Labels = mixedMoment B raw24164step0 raw24164step0Labels := by
      have hz : ∀ j, raw24164 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24164step0 = (fun i j => raw24164 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24164step0 raw24164; decide +kernel
      have hl : raw24164step0Labels = raw24164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24164 raw24164Labels permutation265 hz
    mixedMoment B raw24164step0 raw24164step0Labels = mixedMoment B raw24164step1 raw24164step1Labels := by
      have ha : raw24164step1 = (fun i j => raw24164step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24164step1 raw24164step0; decide +kernel
      have hl : raw24164step1Labels = raw24164step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24164step0 raw24164step0Labels permutation34 permutation7
    mixedMoment B raw24164step1 raw24164step1Labels = mixedMoment B raw24164step2 raw24164step2Labels := by
      have ha : raw24164step2 = raw24164step1 := by apply Matrix.ext; unfold raw24164step2 raw24164step1; decide +kernel
      have hl : raw24164step1Labels = labelEmbedding10 ∘ raw24164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24164step1 raw24164step1Labels raw24164step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw24165 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24165step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24165step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24165 raw24165Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24165 raw24165Labels = mixedMoment B raw24165step0 raw24165step0Labels := by
      have hz : ∀ j, raw24165 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24165step0 = (fun i j => raw24165 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24165step0 raw24165; decide +kernel
      have hl : raw24165step0Labels = raw24165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24165 raw24165Labels permutation265 hz
    mixedMoment B raw24165step0 raw24165step0Labels = mixedMoment B raw24165step1 raw24165step1Labels := by
      have ha : raw24165step1 = (fun i j => raw24165step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24165step1 raw24165step0; decide +kernel
      have hl : raw24165step1Labels = raw24165step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24165step0 raw24165step0Labels permutation32 permutation7
    mixedMoment B raw24165step1 raw24165step1Labels = mixedMoment B raw24165step2 raw24165step2Labels := by
      have ha : raw24165step2 = raw24165step1 := by apply Matrix.ext; unfold raw24165step2 raw24165step1; decide +kernel
      have hl : raw24165step1Labels = labelEmbedding10 ∘ raw24165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24165step1 raw24165step1Labels raw24165step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw24166 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24166step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24166step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24166step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24166step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24166 raw24166Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw24166 raw24166Labels = mixedMoment B raw24166step0 raw24166step0Labels := by
      have hz : ∀ j, raw24166 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24166step0 = (fun i j => raw24166 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24166step0 raw24166; decide +kernel
      have hl : raw24166step0Labels = raw24166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24166 raw24166Labels permutation265 hz
    mixedMoment B raw24166step0 raw24166step0Labels = mixedMoment B raw24166step1 raw24166step1Labels := by
      have ha : raw24166step1 = (fun i j => raw24166step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24166step1 raw24166step0; decide +kernel
      have hl : raw24166step1Labels = raw24166step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24166step0 raw24166step0Labels permutation32 permutation7
    mixedMoment B raw24166step1 raw24166step1Labels = mixedMoment B raw24166step2 raw24166step2Labels := by
      have ha : raw24166step2 = raw24166step1 := by apply Matrix.ext; unfold raw24166step2 raw24166step1; decide +kernel
      have hl : raw24166step1Labels = labelEmbedding10 ∘ raw24166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24166step1 raw24166step1Labels raw24166step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw24167 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24167step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24167step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24167step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24167step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24167step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24167 raw24167Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw24167 raw24167Labels = mixedMoment B raw24167step0 raw24167step0Labels := by
      have hz : ∀ j, raw24167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24167step0 = (fun i j => raw24167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24167step0 raw24167; decide +kernel
      have hl : raw24167step0Labels = raw24167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24167 raw24167Labels permutation346 hz
    mixedMoment B raw24167step0 raw24167step0Labels = mixedMoment B raw24167step1 raw24167step1Labels := by
      have hz : ∀ j, raw24167step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24167step1 = (fun i j => raw24167step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24167step1 raw24167step0; decide +kernel
      have hl : raw24167step1Labels = raw24167step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24167step0 raw24167step0Labels permutation56 hz
    mixedMoment B raw24167step1 raw24167step1Labels = mixedMoment B raw24167step2 raw24167step2Labels := by
      have ha : raw24167step2 = (fun i j => raw24167step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24167step2 raw24167step1; decide +kernel
      have hl : raw24167step2Labels = raw24167step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24167step1 raw24167step1Labels permutation10 permutation6
    mixedMoment B raw24167step2 raw24167step2Labels = mixedMoment B raw24167step3 raw24167step3Labels := by
      have ha : raw24167step3 = raw24167step2 := by apply Matrix.ext; unfold raw24167step3 raw24167step2; decide +kernel
      have hl : raw24167step2Labels = labelEmbedding9 ∘ raw24167step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24167step2 raw24167step2Labels raw24167step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw24168 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24168step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24168step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24168step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24168 raw24168Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24168 raw24168Labels = mixedMoment B raw24168step0 raw24168step0Labels := by
      have hz : ∀ j, raw24168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24168step0 = (fun i j => raw24168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24168step0 raw24168; decide +kernel
      have hl : raw24168step0Labels = raw24168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24168 raw24168Labels permutation346 hz
    mixedMoment B raw24168step0 raw24168step0Labels = mixedMoment B raw24168step1 raw24168step1Labels := by
      have ha : raw24168step1 = (fun i j => raw24168step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24168step1 raw24168step0; decide +kernel
      have hl : raw24168step1Labels = raw24168step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24168step0 raw24168step0Labels permutation34 permutation6
    mixedMoment B raw24168step1 raw24168step1Labels = mixedMoment B raw24168step2 raw24168step2Labels := by
      have ha : raw24168step2 = raw24168step1 := by apply Matrix.ext; unfold raw24168step2 raw24168step1; decide +kernel
      have hl : raw24168step1Labels = labelEmbedding9 ∘ raw24168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24168step1 raw24168step1Labels raw24168step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24169 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24169step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24169step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24169 raw24169Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24169 raw24169Labels = mixedMoment B raw24169step0 raw24169step0Labels := by
      have hz : ∀ j, raw24169 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24169step0 = (fun i j => raw24169 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24169step0 raw24169; decide +kernel
      have hl : raw24169step0Labels = raw24169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24169 raw24169Labels permutation265 hz
    mixedMoment B raw24169step0 raw24169step0Labels = mixedMoment B raw24169step1 raw24169step1Labels := by
      have ha : raw24169step1 = (fun i j => raw24169step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24169step1 raw24169step0; decide +kernel
      have hl : raw24169step1Labels = raw24169step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24169step0 raw24169step0Labels permutation34 permutation6
    mixedMoment B raw24169step1 raw24169step1Labels = mixedMoment B raw24169step2 raw24169step2Labels := by
      have ha : raw24169step2 = raw24169step1 := by apply Matrix.ext; unfold raw24169step2 raw24169step1; decide +kernel
      have hl : raw24169step1Labels = labelEmbedding9 ∘ raw24169step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24169step1 raw24169step1Labels raw24169step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24170 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24170step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24170step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24170step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24170step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24170step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24170 raw24170Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw24170 raw24170Labels = mixedMoment B raw24170step0 raw24170step0Labels := by
      have hz : ∀ j, raw24170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24170step0 = (fun i j => raw24170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24170step0 raw24170; decide +kernel
      have hl : raw24170step0Labels = raw24170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24170 raw24170Labels permutation346 hz
    mixedMoment B raw24170step0 raw24170step0Labels = mixedMoment B raw24170step1 raw24170step1Labels := by
      have hz : ∀ j, raw24170step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24170step1 = (fun i j => raw24170step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24170step1 raw24170step0; decide +kernel
      have hl : raw24170step1Labels = raw24170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24170step0 raw24170step0Labels permutation56 hz
    mixedMoment B raw24170step1 raw24170step1Labels = mixedMoment B raw24170step2 raw24170step2Labels := by
      have ha : raw24170step2 = (fun i j => raw24170step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24170step2 raw24170step1; decide +kernel
      have hl : raw24170step2Labels = raw24170step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24170step1 raw24170step1Labels permutation10 permutation6
    mixedMoment B raw24170step2 raw24170step2Labels = mixedMoment B raw24170step3 raw24170step3Labels := by
      have ha : raw24170step3 = raw24170step2 := by apply Matrix.ext; unfold raw24170step3 raw24170step2; decide +kernel
      have hl : raw24170step2Labels = labelEmbedding9 ∘ raw24170step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24170step2 raw24170step2Labels raw24170step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw24171 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24171step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24171step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24171step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24171step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24171step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24171 raw24171Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw24171 raw24171Labels = mixedMoment B raw24171step0 raw24171step0Labels := by
      have hz : ∀ j, raw24171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24171step0 = (fun i j => raw24171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24171step0 raw24171; decide +kernel
      have hl : raw24171step0Labels = raw24171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24171 raw24171Labels permutation346 hz
    mixedMoment B raw24171step0 raw24171step0Labels = mixedMoment B raw24171step1 raw24171step1Labels := by
      have hz : ∀ j, raw24171step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24171step1 = (fun i j => raw24171step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24171step1 raw24171step0; decide +kernel
      have hl : raw24171step1Labels = raw24171step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24171step0 raw24171step0Labels permutation56 hz
    mixedMoment B raw24171step1 raw24171step1Labels = mixedMoment B raw24171step2 raw24171step2Labels := by
      have ha : raw24171step2 = (fun i j => raw24171step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24171step2 raw24171step1; decide +kernel
      have hl : raw24171step2Labels = raw24171step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24171step1 raw24171step1Labels permutation10 permutation6
    mixedMoment B raw24171step2 raw24171step2Labels = mixedMoment B raw24171step3 raw24171step3Labels := by
      have ha : raw24171step3 = raw24171step2 := by apply Matrix.ext; unfold raw24171step3 raw24171step2; decide +kernel
      have hl : raw24171step2Labels = labelEmbedding9 ∘ raw24171step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24171step2 raw24171step2Labels raw24171step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw24172 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24172step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24172step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24172step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24172step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24172 raw24172Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw24172 raw24172Labels = mixedMoment B raw24172step0 raw24172step0Labels := by
      have hz : ∀ j, raw24172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24172step0 = (fun i j => raw24172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24172step0 raw24172; decide +kernel
      have hl : raw24172step0Labels = raw24172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24172 raw24172Labels permutation346 hz
    mixedMoment B raw24172step0 raw24172step0Labels = mixedMoment B raw24172step1 raw24172step1Labels := by
      have hz : ∀ j, raw24172step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24172step1 = (fun i j => raw24172step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24172step1 raw24172step0; decide +kernel
      have hl : raw24172step1Labels = raw24172step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24172step0 raw24172step0Labels permutation56 hz
    mixedMoment B raw24172step1 raw24172step1Labels = mixedMoment B raw24172step2 raw24172step2Labels := by
      have ha : raw24172step2 = (fun i j => raw24172step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24172step2 raw24172step1; decide +kernel
      have hl : raw24172step2Labels = raw24172step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24172step1 raw24172step1Labels permutation8 permutation6
    mixedMoment B raw24172step2 raw24172step2Labels = mixedMoment B raw24172step3 raw24172step3Labels := by
      have ha : raw24172step3 = raw24172step2 := by apply Matrix.ext; unfold raw24172step3 raw24172step2; decide +kernel
      have hl : raw24172step2Labels = labelEmbedding9 ∘ raw24172step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24172step2 raw24172step2Labels raw24172step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw24173 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24173step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24173step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24173 raw24173Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24173 raw24173Labels = mixedMoment B raw24173step0 raw24173step0Labels := by
      have hz : ∀ j, raw24173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24173step0 = (fun i j => raw24173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24173step0 raw24173; decide +kernel
      have hl : raw24173step0Labels = raw24173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24173 raw24173Labels permutation346 hz
    mixedMoment B raw24173step0 raw24173step0Labels = mixedMoment B raw24173step1 raw24173step1Labels := by
      have ha : raw24173step1 = (fun i j => raw24173step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24173step1 raw24173step0; decide +kernel
      have hl : raw24173step1Labels = raw24173step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24173step0 raw24173step0Labels permutation32 permutation6
    mixedMoment B raw24173step1 raw24173step1Labels = mixedMoment B raw24173step2 raw24173step2Labels := by
      have ha : raw24173step2 = raw24173step1 := by apply Matrix.ext; unfold raw24173step2 raw24173step1; decide +kernel
      have hl : raw24173step1Labels = labelEmbedding9 ∘ raw24173step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24173step1 raw24173step1Labels raw24173step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24174 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24174step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24174step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24174 raw24174Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24174 raw24174Labels = mixedMoment B raw24174step0 raw24174step0Labels := by
      have hz : ∀ j, raw24174 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24174step0 = (fun i j => raw24174 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24174step0 raw24174; decide +kernel
      have hl : raw24174step0Labels = raw24174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24174 raw24174Labels permutation265 hz
    mixedMoment B raw24174step0 raw24174step0Labels = mixedMoment B raw24174step1 raw24174step1Labels := by
      have ha : raw24174step1 = (fun i j => raw24174step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24174step1 raw24174step0; decide +kernel
      have hl : raw24174step1Labels = raw24174step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24174step0 raw24174step0Labels permutation32 permutation6
    mixedMoment B raw24174step1 raw24174step1Labels = mixedMoment B raw24174step2 raw24174step2Labels := by
      have ha : raw24174step2 = raw24174step1 := by apply Matrix.ext; unfold raw24174step2 raw24174step1; decide +kernel
      have hl : raw24174step1Labels = labelEmbedding9 ∘ raw24174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24174step1 raw24174step1Labels raw24174step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24175 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24175step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24175step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24175step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24175step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24175step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24175step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24175 raw24175Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw24175 raw24175Labels = mixedMoment B raw24175step0 raw24175step0Labels := by
      have hz : ∀ j, raw24175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24175step0 = (fun i j => raw24175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24175step0 raw24175; decide +kernel
      have hl : raw24175step0Labels = raw24175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24175 raw24175Labels permutation346 hz
    mixedMoment B raw24175step0 raw24175step0Labels = mixedMoment B raw24175step1 raw24175step1Labels := by
      have hz : ∀ j, raw24175step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24175step1 = (fun i j => raw24175step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24175step1 raw24175step0; decide +kernel
      have hl : raw24175step1Labels = raw24175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24175step0 raw24175step0Labels permutation56 hz
    mixedMoment B raw24175step1 raw24175step1Labels = mixedMoment B raw24175step2 raw24175step2Labels := by
      have ha : raw24175step2 = (fun i j => raw24175step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24175step2 raw24175step1; decide +kernel
      have hl : raw24175step2Labels = raw24175step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24175step1 raw24175step1Labels permutation8 permutation6
    mixedMoment B raw24175step2 raw24175step2Labels = mixedMoment B raw24175step3 raw24175step3Labels := by
      have ha : raw24175step3 = raw24175step2 := by apply Matrix.ext; unfold raw24175step3 raw24175step2; decide +kernel
      have hl : raw24175step2Labels = labelEmbedding9 ∘ raw24175step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24175step2 raw24175step2Labels raw24175step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw24176 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24176step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24176step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24176step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24176step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24176 raw24176Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw24176 raw24176Labels = mixedMoment B raw24176step0 raw24176step0Labels := by
      have hz : ∀ j, raw24176 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24176step0 = (fun i j => raw24176 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24176step0 raw24176; decide +kernel
      have hl : raw24176step0Labels = raw24176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24176 raw24176Labels permutation346 hz
    mixedMoment B raw24176step0 raw24176step0Labels = mixedMoment B raw24176step1 raw24176step1Labels := by
      have hz : ∀ j, raw24176step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24176step1 = (fun i j => raw24176step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24176step1 raw24176step0; decide +kernel
      have hl : raw24176step1Labels = raw24176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24176step0 raw24176step0Labels permutation56 hz
    mixedMoment B raw24176step1 raw24176step1Labels = mixedMoment B raw24176step2 raw24176step2Labels := by
      have ha : raw24176step2 = (fun i j => raw24176step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24176step2 raw24176step1; decide +kernel
      have hl : raw24176step2Labels = raw24176step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24176step1 raw24176step1Labels permutation8 permutation6
    mixedMoment B raw24176step2 raw24176step2Labels = mixedMoment B raw24176step3 raw24176step3Labels := by
      have ha : raw24176step3 = raw24176step2 := by apply Matrix.ext; unfold raw24176step3 raw24176step2; decide +kernel
      have hl : raw24176step2Labels = labelEmbedding9 ∘ raw24176step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24176step2 raw24176step2Labels raw24176step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw24177 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24177step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24177step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24177step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw24177step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24177step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw24177step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24177 raw24177Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw24177 raw24177Labels = mixedMoment B raw24177step0 raw24177step0Labels := by
      have hz : ∀ j, raw24177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24177step0 = (fun i j => raw24177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24177step0 raw24177; decide +kernel
      have hl : raw24177step0Labels = raw24177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24177 raw24177Labels permutation346 hz
    mixedMoment B raw24177step0 raw24177step0Labels = mixedMoment B raw24177step1 raw24177step1Labels := by
      have hz : ∀ j, raw24177step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24177step1 = (fun i j => raw24177step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24177step1 raw24177step0; decide +kernel
      have hl : raw24177step1Labels = raw24177step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24177step0 raw24177step0Labels permutation56 hz
    mixedMoment B raw24177step1 raw24177step1Labels = mixedMoment B raw24177step2 raw24177step2Labels := by
      have ha : raw24177step2 = (fun i j => raw24177step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24177step2 raw24177step1; decide +kernel
      have hl : raw24177step2Labels = raw24177step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24177step1 raw24177step1Labels permutation8 permutation6
    mixedMoment B raw24177step2 raw24177step2Labels = mixedMoment B raw24177step3 raw24177step3Labels := by
      have ha : raw24177step3 = raw24177step2 := by apply Matrix.ext; unfold raw24177step3 raw24177step2; decide +kernel
      have hl : raw24177step2Labels = labelEmbedding9 ∘ raw24177step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24177step2 raw24177step2Labels raw24177step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw24178 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24178step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw24178step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw24178step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24178 raw24178Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw24178 raw24178Labels = mixedMoment B raw24178step0 raw24178step0Labels := by
      have hz : ∀ j, raw24178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24178step0 = (fun i j => raw24178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24178step0 raw24178; decide +kernel
      have hl : raw24178step0Labels = raw24178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24178 raw24178Labels permutation346 hz
    mixedMoment B raw24178step0 raw24178step0Labels = mixedMoment B raw24178step1 raw24178step1Labels := by
      have ha : raw24178step1 = (fun i j => raw24178step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24178step1 raw24178step0; decide +kernel
      have hl : raw24178step1Labels = raw24178step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24178step0 raw24178step0Labels permutation32 permutation6
    mixedMoment B raw24178step1 raw24178step1Labels = mixedMoment B raw24178step2 raw24178step2Labels := by
      have ha : raw24178step2 = raw24178step1 := by apply Matrix.ext; unfold raw24178step2 raw24178step1; decide +kernel
      have hl : raw24178step1Labels = labelEmbedding9 ∘ raw24178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24178step1 raw24178step1Labels raw24178step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw24179 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24179step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw24179step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw24179step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24179 raw24179Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw24179 raw24179Labels = mixedMoment B raw24179step0 raw24179step0Labels := by
      have hz : ∀ j, raw24179 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24179step0 = (fun i j => raw24179 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24179step0 raw24179; decide +kernel
      have hl : raw24179step0Labels = raw24179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24179 raw24179Labels permutation265 hz
    mixedMoment B raw24179step0 raw24179step0Labels = mixedMoment B raw24179step1 raw24179step1Labels := by
      have ha : raw24179step1 = (fun i j => raw24179step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24179step1 raw24179step0; decide +kernel
      have hl : raw24179step1Labels = raw24179step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24179step0 raw24179step0Labels permutation32 permutation6
    mixedMoment B raw24179step1 raw24179step1Labels = mixedMoment B raw24179step2 raw24179step2Labels := by
      have ha : raw24179step2 = raw24179step1 := by apply Matrix.ext; unfold raw24179step2 raw24179step1; decide +kernel
      have hl : raw24179step1Labels = labelEmbedding9 ∘ raw24179step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24179step1 raw24179step1Labels raw24179step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw24180 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24180step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24180step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24180step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24180step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24180step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24180 raw24180Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw24180 raw24180Labels = mixedMoment B raw24180step0 raw24180step0Labels := by
      have hz : ∀ j, raw24180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24180step0 = (fun i j => raw24180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24180step0 raw24180; decide +kernel
      have hl : raw24180step0Labels = raw24180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24180 raw24180Labels permutation346 hz
    mixedMoment B raw24180step0 raw24180step0Labels = mixedMoment B raw24180step1 raw24180step1Labels := by
      have hz : ∀ j, raw24180step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24180step1 = (fun i j => raw24180step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24180step1 raw24180step0; decide +kernel
      have hl : raw24180step1Labels = raw24180step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24180step0 raw24180step0Labels permutation56 hz
    mixedMoment B raw24180step1 raw24180step1Labels = mixedMoment B raw24180step2 raw24180step2Labels := by
      have ha : raw24180step2 = (fun i j => raw24180step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24180step2 raw24180step1; decide +kernel
      have hl : raw24180step2Labels = raw24180step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24180step1 raw24180step1Labels permutation8 permutation6
    mixedMoment B raw24180step2 raw24180step2Labels = mixedMoment B raw24180step3 raw24180step3Labels := by
      have ha : raw24180step3 = raw24180step2 := by apply Matrix.ext; unfold raw24180step3 raw24180step2; decide +kernel
      have hl : raw24180step2Labels = labelEmbedding9 ∘ raw24180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24180step2 raw24180step2Labels raw24180step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw24181 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24181step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24181step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24181 raw24181Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw24181 raw24181Labels = mixedMoment B raw24181step0 raw24181step0Labels := by
      have hz : ∀ j, raw24181 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24181step0 = (fun i j => raw24181 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24181step0 raw24181; decide +kernel
      have hl : raw24181step0Labels = raw24181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24181 raw24181Labels permutation346 hz
    mixedMoment B raw24181step0 raw24181step0Labels = mixedMoment B raw24181step1 raw24181step1Labels := by
      have hz : ∀ j, raw24181step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24181step1 = (fun i j => raw24181step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24181step1 raw24181step0; decide +kernel
      have hl : raw24181step1Labels = raw24181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24181step0 raw24181step0Labels permutation56 hz
    mixedMoment B raw24181step1 raw24181step1Labels = mixedMoment B raw24181step2 raw24181step2Labels := by
      have ha : raw24181step2 = (fun i j => raw24181step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24181step2 raw24181step1; decide +kernel
      have hl : raw24181step2Labels = raw24181step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24181step1 raw24181step1Labels permutation10 permutation6
    mixedMoment B raw24181step2 raw24181step2Labels = mixedMoment B raw24181step3 raw24181step3Labels := by
      have ha : raw24181step3 = raw24181step2 := by apply Matrix.ext; unfold raw24181step3 raw24181step2; decide +kernel
      have hl : raw24181step2Labels = labelEmbedding9 ∘ raw24181step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24181step2 raw24181step2Labels raw24181step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw24182 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24182 raw24182Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw24182 raw24182Labels = mixedMoment B raw24182step0 raw24182step0Labels := by
      have hz : ∀ j, raw24182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24182step0 = (fun i j => raw24182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24182step0 raw24182; decide +kernel
      have hl : raw24182step0Labels = raw24182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24182 raw24182Labels permutation346 hz
    mixedMoment B raw24182step0 raw24182step0Labels = mixedMoment B raw24182step1 raw24182step1Labels := by
      have ha : raw24182step1 = (fun i j => raw24182step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24182step1 raw24182step0; decide +kernel
      have hl : raw24182step1Labels = raw24182step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24182step0 raw24182step0Labels permutation32 permutation7
    mixedMoment B raw24182step1 raw24182step1Labels = mixedMoment B raw24182step2 raw24182step2Labels := by
      have ha : raw24182step2 = raw24182step1 := by apply Matrix.ext; unfold raw24182step2 raw24182step1; decide +kernel
      have hl : raw24182step1Labels = labelEmbedding1 ∘ raw24182step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24182step1 raw24182step1Labels raw24182step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw24183 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24183step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24183 raw24183Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw24183 raw24183Labels = mixedMoment B raw24183step0 raw24183step0Labels := by
      have hz : ∀ j, raw24183 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24183step0 = (fun i j => raw24183 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24183step0 raw24183; decide +kernel
      have hl : raw24183step0Labels = raw24183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24183 raw24183Labels permutation265 hz
    mixedMoment B raw24183step0 raw24183step0Labels = mixedMoment B raw24183step1 raw24183step1Labels := by
      have ha : raw24183step1 = (fun i j => raw24183step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24183step1 raw24183step0; decide +kernel
      have hl : raw24183step1Labels = raw24183step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24183step0 raw24183step0Labels permutation32 permutation7
    mixedMoment B raw24183step1 raw24183step1Labels = mixedMoment B raw24183step2 raw24183step2Labels := by
      have ha : raw24183step2 = raw24183step1 := by apply Matrix.ext; unfold raw24183step2 raw24183step1; decide +kernel
      have hl : raw24183step1Labels = labelEmbedding1 ∘ raw24183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24183step1 raw24183step1Labels raw24183step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw24184 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24184step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24184step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24184step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24184 raw24184Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw24184 raw24184Labels = mixedMoment B raw24184step0 raw24184step0Labels := by
      have hz : ∀ j, raw24184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24184step0 = (fun i j => raw24184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24184step0 raw24184; decide +kernel
      have hl : raw24184step0Labels = raw24184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24184 raw24184Labels permutation346 hz
    mixedMoment B raw24184step0 raw24184step0Labels = mixedMoment B raw24184step1 raw24184step1Labels := by
      have hz : ∀ j, raw24184step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24184step1 = (fun i j => raw24184step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24184step1 raw24184step0; decide +kernel
      have hl : raw24184step1Labels = raw24184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24184step0 raw24184step0Labels permutation56 hz
    mixedMoment B raw24184step1 raw24184step1Labels = mixedMoment B raw24184step2 raw24184step2Labels := by
      have ha : raw24184step2 = (fun i j => raw24184step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24184step2 raw24184step1; decide +kernel
      have hl : raw24184step2Labels = raw24184step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24184step1 raw24184step1Labels permutation10 permutation7
    mixedMoment B raw24184step2 raw24184step2Labels = mixedMoment B raw24184step3 raw24184step3Labels := by
      have ha : raw24184step3 = raw24184step2 := by apply Matrix.ext; unfold raw24184step3 raw24184step2; decide +kernel
      have hl : raw24184step2Labels = labelEmbedding1 ∘ raw24184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24184step2 raw24184step2Labels raw24184step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw24185 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24185step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24185step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24185step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24185 raw24185Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw24185 raw24185Labels = mixedMoment B raw24185step0 raw24185step0Labels := by
      have hz : ∀ j, raw24185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24185step0 = (fun i j => raw24185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24185step0 raw24185; decide +kernel
      have hl : raw24185step0Labels = raw24185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24185 raw24185Labels permutation346 hz
    mixedMoment B raw24185step0 raw24185step0Labels = mixedMoment B raw24185step1 raw24185step1Labels := by
      have hz : ∀ j, raw24185step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24185step1 = (fun i j => raw24185step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24185step1 raw24185step0; decide +kernel
      have hl : raw24185step1Labels = raw24185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24185step0 raw24185step0Labels permutation56 hz
    mixedMoment B raw24185step1 raw24185step1Labels = mixedMoment B raw24185step2 raw24185step2Labels := by
      have ha : raw24185step2 = (fun i j => raw24185step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24185step2 raw24185step1; decide +kernel
      have hl : raw24185step2Labels = raw24185step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24185step1 raw24185step1Labels permutation8 permutation7
    mixedMoment B raw24185step2 raw24185step2Labels = mixedMoment B raw24185step3 raw24185step3Labels := by
      have ha : raw24185step3 = raw24185step2 := by apply Matrix.ext; unfold raw24185step3 raw24185step2; decide +kernel
      have hl : raw24185step2Labels = labelEmbedding1 ∘ raw24185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24185step2 raw24185step2Labels raw24185step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw24186 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24186step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24186step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24186step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24186 raw24186Labels = mixedMoment B node1086 node1086Labels := by
  calc
    mixedMoment B raw24186 raw24186Labels = mixedMoment B raw24186step0 raw24186step0Labels := by
      have hz : ∀ j, raw24186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24186step0 = (fun i j => raw24186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24186step0 raw24186; decide +kernel
      have hl : raw24186step0Labels = raw24186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24186 raw24186Labels permutation346 hz
    mixedMoment B raw24186step0 raw24186step0Labels = mixedMoment B raw24186step1 raw24186step1Labels := by
      have hz : ∀ j, raw24186step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24186step1 = (fun i j => raw24186step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24186step1 raw24186step0; decide +kernel
      have hl : raw24186step1Labels = raw24186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24186step0 raw24186step0Labels permutation56 hz
    mixedMoment B raw24186step1 raw24186step1Labels = mixedMoment B raw24186step2 raw24186step2Labels := by
      have ha : raw24186step2 = (fun i j => raw24186step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24186step2 raw24186step1; decide +kernel
      have hl : raw24186step2Labels = raw24186step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24186step1 raw24186step1Labels permutation8 permutation7
    mixedMoment B raw24186step2 raw24186step2Labels = mixedMoment B raw24186step3 raw24186step3Labels := by
      have ha : raw24186step3 = raw24186step2 := by apply Matrix.ext; unfold raw24186step3 raw24186step2; decide +kernel
      have hl : raw24186step2Labels = labelEmbedding1 ∘ raw24186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24186step2 raw24186step2Labels raw24186step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1086 node1086Labels := by rfl

def raw24187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24187step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24187 raw24187Labels = mixedMoment B node1414 node1414Labels := by
  calc
    mixedMoment B raw24187 raw24187Labels = mixedMoment B raw24187step0 raw24187step0Labels := by
      have hz : ∀ j, raw24187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24187step0 = (fun i j => raw24187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24187step0 raw24187; decide +kernel
      have hl : raw24187step0Labels = raw24187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24187 raw24187Labels permutation346 hz
    mixedMoment B raw24187step0 raw24187step0Labels = mixedMoment B raw24187step1 raw24187step1Labels := by
      have ha : raw24187step1 = (fun i j => raw24187step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24187step1 raw24187step0; decide +kernel
      have hl : raw24187step1Labels = raw24187step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24187step0 raw24187step0Labels permutation32 permutation7
    mixedMoment B raw24187step1 raw24187step1Labels = mixedMoment B raw24187step2 raw24187step2Labels := by
      have ha : raw24187step2 = raw24187step1 := by apply Matrix.ext; unfold raw24187step2 raw24187step1; decide +kernel
      have hl : raw24187step1Labels = labelEmbedding1 ∘ raw24187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24187step1 raw24187step1Labels raw24187step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1414 node1414Labels := by rfl

def raw24188 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24188 raw24188Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw24188 raw24188Labels = mixedMoment B raw24188step0 raw24188step0Labels := by
      have ha : raw24188step0 = (fun i j => raw24188 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24188step0 raw24188; decide +kernel
      have hl : raw24188step0Labels = raw24188Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24188 raw24188Labels permutation152 permutation7
    mixedMoment B raw24188step0 raw24188step0Labels = mixedMoment B raw24188step1 raw24188step1Labels := by
      have ha : raw24188step1 = raw24188step0 := by apply Matrix.ext; unfold raw24188step1 raw24188step0; decide +kernel
      have hl : raw24188step0Labels = labelEmbedding1 ∘ raw24188step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24188step0 raw24188step0Labels raw24188step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1216 node1216Labels := by rfl

def raw24189 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24189 raw24189Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw24189 raw24189Labels = mixedMoment B raw24189step0 raw24189step0Labels := by
      have hz : ∀ j, raw24189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24189step0 = (fun i j => raw24189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24189step0 raw24189; decide +kernel
      have hl : raw24189step0Labels = raw24189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24189 raw24189Labels permutation346 hz
    mixedMoment B raw24189step0 raw24189step0Labels = mixedMoment B raw24189step1 raw24189step1Labels := by
      have ha : raw24189step1 = (fun i j => raw24189step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24189step1 raw24189step0; decide +kernel
      have hl : raw24189step1Labels = raw24189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24189step0 raw24189step0Labels permutation34 permutation7
    mixedMoment B raw24189step1 raw24189step1Labels = mixedMoment B raw24189step2 raw24189step2Labels := by
      have ha : raw24189step2 = raw24189step1 := by apply Matrix.ext; unfold raw24189step2 raw24189step1; decide +kernel
      have hl : raw24189step1Labels = labelEmbedding1 ∘ raw24189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24189step1 raw24189step1Labels raw24189step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw24190 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24190 raw24190Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw24190 raw24190Labels = mixedMoment B raw24190step0 raw24190step0Labels := by
      have hz : ∀ j, raw24190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24190step0 = (fun i j => raw24190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24190step0 raw24190; decide +kernel
      have hl : raw24190step0Labels = raw24190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24190 raw24190Labels permutation346 hz
    mixedMoment B raw24190step0 raw24190step0Labels = mixedMoment B raw24190step1 raw24190step1Labels := by
      have ha : raw24190step1 = (fun i j => raw24190step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24190step1 raw24190step0; decide +kernel
      have hl : raw24190step1Labels = raw24190step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24190step0 raw24190step0Labels permutation32 permutation7
    mixedMoment B raw24190step1 raw24190step1Labels = mixedMoment B raw24190step2 raw24190step2Labels := by
      have ha : raw24190step2 = raw24190step1 := by apply Matrix.ext; unfold raw24190step2 raw24190step1; decide +kernel
      have hl : raw24190step1Labels = labelEmbedding1 ∘ raw24190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24190step1 raw24190step1Labels raw24190step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw24191 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24191 raw24191Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw24191 raw24191Labels = mixedMoment B raw24191step0 raw24191step0Labels := by
      have hz : ∀ j, raw24191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24191step0 = (fun i j => raw24191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24191step0 raw24191; decide +kernel
      have hl : raw24191step0Labels = raw24191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24191 raw24191Labels permutation346 hz
    mixedMoment B raw24191step0 raw24191step0Labels = mixedMoment B raw24191step1 raw24191step1Labels := by
      have ha : raw24191step1 = (fun i j => raw24191step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24191step1 raw24191step0; decide +kernel
      have hl : raw24191step1Labels = raw24191step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24191step0 raw24191step0Labels permutation32 permutation7
    mixedMoment B raw24191step1 raw24191step1Labels = mixedMoment B raw24191step2 raw24191step2Labels := by
      have ha : raw24191step2 = raw24191step1 := by apply Matrix.ext; unfold raw24191step2 raw24191step1; decide +kernel
      have hl : raw24191step1Labels = labelEmbedding1 ∘ raw24191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24191step1 raw24191step1Labels raw24191step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1240 node1240Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
