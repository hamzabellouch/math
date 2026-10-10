import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26880 raw26880Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw26880 raw26880Labels = mixedMoment B raw26880step0 raw26880step0Labels := by
      have ha : raw26880step0 = (fun i j => raw26880 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26880step0 raw26880; decide +kernel
      have hl : raw26880step0Labels = raw26880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26880 raw26880Labels permutation156 permutation2
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw26881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26881 raw26881Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw26881 raw26881Labels = mixedMoment B raw26881step0 raw26881step0Labels := by
      have ha : raw26881step0 = (fun i j => raw26881 (permutation163 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26881step0 raw26881; decide +kernel
      have hl : raw26881step0Labels = raw26881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26881 raw26881Labels permutation163 permutation2
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw26882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26882 raw26882Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw26882 raw26882Labels = mixedMoment B raw26882step0 raw26882step0Labels := by
      have ha : raw26882step0 = (fun i j => raw26882 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26882step0 raw26882; decide +kernel
      have hl : raw26882step0Labels = raw26882Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26882 raw26882Labels permutation169 permutation2
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw26883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26883 raw26883Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw26883 raw26883Labels = mixedMoment B raw26883step0 raw26883step0Labels := by
      have hz : ∀ j, raw26883 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26883step0 = (fun i j => raw26883 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26883step0 raw26883; decide +kernel
      have hl : raw26883step0Labels = raw26883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26883 raw26883Labels permutation590 hz
    mixedMoment B raw26883step0 raw26883step0Labels = mixedMoment B raw26883step1 raw26883step1Labels := by
      have ha : raw26883step1 = (fun i j => raw26883step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26883step1 raw26883step0; decide +kernel
      have hl : raw26883step1Labels = raw26883step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26883step0 raw26883step0Labels permutation35 permutation2
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw26884 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1], ![0, 0]]
def raw26884Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26884step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw26884step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26884step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw26884step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26884 raw26884Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw26884 raw26884Labels = mixedMoment B raw26884step0 raw26884step0Labels := by
      have hz : ∀ j, raw26884 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26884step0 = (fun i j => raw26884 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26884step0 raw26884; decide +kernel
      have hl : raw26884step0Labels = raw26884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26884 raw26884Labels permutation590 hz
    mixedMoment B raw26884step0 raw26884step0Labels = mixedMoment B raw26884step1 raw26884step1Labels := by
      have ha : raw26884step1 = (fun i j => raw26884step0 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26884step1 raw26884step0; decide +kernel
      have hl : raw26884step1Labels = raw26884step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26884step0 raw26884step0Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw26885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26885 raw26885Labels = mixedMoment B node1187 node1187Labels := by
  calc
    _ = mixedMoment B node1187 node1187Labels := by rfl

def raw26886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26886 raw26886Labels = mixedMoment B node2402 node2402Labels := by
  calc
    _ = mixedMoment B node2402 node2402Labels := by rfl

def raw26887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26887 raw26887Labels = mixedMoment B node2671 node2671Labels := by
  calc
    _ = mixedMoment B node2671 node2671Labels := by rfl

def raw26888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26888 raw26888Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw26888 raw26888Labels = mixedMoment B raw26888step0 raw26888step0Labels := by
      have ha : raw26888step0 = (fun i j => raw26888 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26888step0 raw26888; decide +kernel
      have hl : raw26888step0Labels = raw26888Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26888 raw26888Labels permutation158 permutation2
    _ = mixedMoment B node2671 node2671Labels := by rfl

def raw26889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw26889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26889 raw26889Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw26889 raw26889Labels = mixedMoment B raw26889step0 raw26889step0Labels := by
      have ha : raw26889step0 = (fun i j => raw26889 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26889step0 raw26889; decide +kernel
      have hl : raw26889step0Labels = raw26889Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26889 raw26889Labels permutation164 permutation2
    _ = mixedMoment B node2671 node2671Labels := by rfl

def raw26890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw26890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26890 raw26890Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw26890 raw26890Labels = mixedMoment B raw26890step0 raw26890step0Labels := by
      have ha : raw26890step0 = (fun i j => raw26890 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26890step0 raw26890; decide +kernel
      have hl : raw26890step0Labels = raw26890Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26890 raw26890Labels permutation170 permutation2
    _ = mixedMoment B node2671 node2671Labels := by rfl

def raw26891 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26891Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26891 raw26891Labels = mixedMoment B node4087 node4087Labels := by
  calc
    _ = mixedMoment B node4087 node4087Labels := by rfl

def raw26892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26892 raw26892Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw26892 raw26892Labels = mixedMoment B raw26892step0 raw26892step0Labels := by
      have ha : raw26892step0 = (fun i j => raw26892 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26892step0 raw26892; decide +kernel
      have hl : raw26892step0Labels = raw26892Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26892 raw26892Labels permutation161 permutation2
    _ = mixedMoment B node1100 node1100Labels := by rfl

def raw26893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26893 raw26893Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw26893 raw26893Labels = mixedMoment B raw26893step0 raw26893step0Labels := by
      have ha : raw26893step0 = (fun i j => raw26893 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26893step0 raw26893; decide +kernel
      have hl : raw26893step0Labels = raw26893Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26893 raw26893Labels permutation155 permutation2
    _ = mixedMoment B node1100 node1100Labels := by rfl

def raw26894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26894 raw26894Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw26894 raw26894Labels = mixedMoment B raw26894step0 raw26894step0Labels := by
      have ha : raw26894step0 = (fun i j => raw26894 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26894step0 raw26894; decide +kernel
      have hl : raw26894step0Labels = raw26894Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26894 raw26894Labels permutation153 permutation2
    _ = mixedMoment B node1100 node1100Labels := by rfl

def raw26895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26895 raw26895Labels = mixedMoment B node1100 node1100Labels := by
  calc
    _ = mixedMoment B node1100 node1100Labels := by rfl

def raw26896 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26896step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26896 raw26896Labels = mixedMoment B node3244 node3244Labels := by
  calc
    mixedMoment B raw26896 raw26896Labels = mixedMoment B raw26896step0 raw26896step0Labels := by
      have ha : raw26896step0 = (fun i j => raw26896 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26896step0 raw26896; decide +kernel
      have hl : raw26896step0Labels = raw26896Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26896 raw26896Labels permutation152 permutation4
    mixedMoment B raw26896step0 raw26896step0Labels = mixedMoment B raw26896step1 raw26896step1Labels := by
      have ha : raw26896step1 = -raw26896step0 := by apply Matrix.ext; change ∀ i j, raw26896step1 i j = -(raw26896step0 i j); unfold raw26896step1 raw26896step0; decide +kernel
      have hl : raw26896step1Labels = raw26896step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3244 node3244Labels := by rfl

def raw26897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26897 raw26897Labels = mixedMoment B node1621 node1621Labels := by
  calc
    mixedMoment B raw26897 raw26897Labels = mixedMoment B raw26897step0 raw26897step0Labels := by
      have ha : raw26897step0 = (fun i j => raw26897 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26897step0 raw26897; decide +kernel
      have hl : raw26897step0Labels = raw26897Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26897 raw26897Labels permutation152 permutation4
    mixedMoment B raw26897step0 raw26897step0Labels = mixedMoment B raw26897step1 raw26897step1Labels := by
      have ha : raw26897step1 = -raw26897step0 := by apply Matrix.ext; change ∀ i j, raw26897step1 i j = -(raw26897step0 i j); unfold raw26897step1 raw26897step0; decide +kernel
      have hl : raw26897step1Labels = raw26897step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1621 node1621Labels := by rfl

def raw26898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26898 raw26898Labels = mixedMoment B node1545 node1545Labels := by
  calc
    mixedMoment B raw26898 raw26898Labels = mixedMoment B raw26898step0 raw26898step0Labels := by
      have ha : raw26898step0 = (fun i j => raw26898 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26898step0 raw26898; decide +kernel
      have hl : raw26898step0Labels = raw26898Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26898 raw26898Labels permutation161 permutation4
    mixedMoment B raw26898step0 raw26898step0Labels = mixedMoment B raw26898step1 raw26898step1Labels := by
      have ha : raw26898step1 = -raw26898step0 := by apply Matrix.ext; change ∀ i j, raw26898step1 i j = -(raw26898step0 i j); unfold raw26898step1 raw26898step0; decide +kernel
      have hl : raw26898step1Labels = raw26898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1545 node1545Labels := by rfl

def raw26899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26899 raw26899Labels = mixedMoment B node1545 node1545Labels := by
  calc
    mixedMoment B raw26899 raw26899Labels = mixedMoment B raw26899step0 raw26899step0Labels := by
      have ha : raw26899step0 = (fun i j => raw26899 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26899step0 raw26899; decide +kernel
      have hl : raw26899step0Labels = raw26899Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26899 raw26899Labels permutation155 permutation4
    mixedMoment B raw26899step0 raw26899step0Labels = mixedMoment B raw26899step1 raw26899step1Labels := by
      have ha : raw26899step1 = -raw26899step0 := by apply Matrix.ext; change ∀ i j, raw26899step1 i j = -(raw26899step0 i j); unfold raw26899step1 raw26899step0; decide +kernel
      have hl : raw26899step1Labels = raw26899step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1545 node1545Labels := by rfl

def raw26900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26900 raw26900Labels = mixedMoment B node1545 node1545Labels := by
  calc
    mixedMoment B raw26900 raw26900Labels = mixedMoment B raw26900step0 raw26900step0Labels := by
      have ha : raw26900step0 = (fun i j => raw26900 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26900step0 raw26900; decide +kernel
      have hl : raw26900step0Labels = raw26900Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26900 raw26900Labels permutation153 permutation4
    mixedMoment B raw26900step0 raw26900step0Labels = mixedMoment B raw26900step1 raw26900step1Labels := by
      have ha : raw26900step1 = -raw26900step0 := by apply Matrix.ext; change ∀ i j, raw26900step1 i j = -(raw26900step0 i j); unfold raw26900step1 raw26900step0; decide +kernel
      have hl : raw26900step1Labels = raw26900step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1545 node1545Labels := by rfl

def raw26901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26901 raw26901Labels = mixedMoment B node1545 node1545Labels := by
  calc
    mixedMoment B raw26901 raw26901Labels = mixedMoment B raw26901step0 raw26901step0Labels := by
      have ha : raw26901step0 = (fun i j => raw26901 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26901step0 raw26901; decide +kernel
      have hl : raw26901step0Labels = raw26901Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26901 raw26901Labels permutation152 permutation4
    mixedMoment B raw26901step0 raw26901step0Labels = mixedMoment B raw26901step1 raw26901step1Labels := by
      have ha : raw26901step1 = -raw26901step0 := by apply Matrix.ext; change ∀ i j, raw26901step1 i j = -(raw26901step0 i j); unfold raw26901step1 raw26901step0; decide +kernel
      have hl : raw26901step1Labels = raw26901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1545 node1545Labels := by rfl

def raw26902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26902 raw26902Labels = mixedMoment B node1052 node1052Labels := by
  calc
    mixedMoment B raw26902 raw26902Labels = mixedMoment B raw26902step0 raw26902step0Labels := by
      have ha : raw26902step0 = (fun i j => raw26902 (permutation174 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26902step0 raw26902; decide +kernel
      have hl : raw26902step0Labels = raw26902Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26902 raw26902Labels permutation174 permutation2
    _ = mixedMoment B node1052 node1052Labels := by rfl

def raw26903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26903 raw26903Labels = mixedMoment B node2127 node2127Labels := by
  calc
    mixedMoment B raw26903 raw26903Labels = mixedMoment B raw26903step0 raw26903step0Labels := by
      have ha : raw26903step0 = (fun i j => raw26903 (permutation174 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26903step0 raw26903; decide +kernel
      have hl : raw26903step0Labels = raw26903Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26903 raw26903Labels permutation174 permutation2
    _ = mixedMoment B node2127 node2127Labels := by rfl

def raw26904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw26904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26904 raw26904Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw26904 raw26904Labels = mixedMoment B raw26904step0 raw26904step0Labels := by
      have ha : raw26904step0 = (fun i j => raw26904 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26904step0 raw26904; decide +kernel
      have hl : raw26904step0Labels = raw26904Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26904 raw26904Labels permutation181 permutation2
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw26905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw26905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26905 raw26905Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw26905 raw26905Labels = mixedMoment B raw26905step0 raw26905step0Labels := by
      have ha : raw26905step0 = (fun i j => raw26905 (permutation205 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26905step0 raw26905; decide +kernel
      have hl : raw26905step0Labels = raw26905Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26905 raw26905Labels permutation205 permutation2
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw26906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1]]
def raw26906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26906 raw26906Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw26906 raw26906Labels = mixedMoment B raw26906step0 raw26906step0Labels := by
      have hz : ∀ j, raw26906 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26906step0 = (fun i j => raw26906 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26906step0 raw26906; decide +kernel
      have hl : raw26906step0Labels = raw26906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26906 raw26906Labels permutation520 hz
    mixedMoment B raw26906step0 raw26906step0Labels = mixedMoment B raw26906step1 raw26906step1Labels := by
      have ha : raw26906step1 = (fun i j => raw26906step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26906step1 raw26906step0; decide +kernel
      have hl : raw26906step1Labels = raw26906step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26906step0 raw26906step0Labels permutation36 permutation2
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw26907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1]]
def raw26907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26907 raw26907Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw26907 raw26907Labels = mixedMoment B raw26907step0 raw26907step0Labels := by
      have ha : raw26907step0 = (fun i j => raw26907 (permutation250 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26907step0 raw26907; decide +kernel
      have hl : raw26907step0Labels = raw26907Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26907 raw26907Labels permutation250 permutation2
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw26908 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]
def raw26908Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26908step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![1, -1], ![-1, 1]]
def raw26908step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26908step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26908step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26908 raw26908Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw26908 raw26908Labels = mixedMoment B raw26908step0 raw26908step0Labels := by
      have hz : ∀ j, raw26908 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26908step0 = (fun i j => raw26908 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26908step0 raw26908; decide +kernel
      have hl : raw26908step0Labels = raw26908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26908 raw26908Labels permutation520 hz
    mixedMoment B raw26908step0 raw26908step0Labels = mixedMoment B raw26908step1 raw26908step1Labels := by
      have ha : raw26908step1 = (fun i j => raw26908step0 (permutation53 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26908step1 raw26908step0; decide +kernel
      have hl : raw26908step1Labels = raw26908step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26908step0 raw26908step0Labels permutation53 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw26909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26909 raw26909Labels = mixedMoment B node1032 node1032Labels := by
  calc
    mixedMoment B raw26909 raw26909Labels = mixedMoment B raw26909step0 raw26909step0Labels := by
      have ha : raw26909step0 = (fun i j => raw26909 (permutation175 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26909step0 raw26909; decide +kernel
      have hl : raw26909step0Labels = raw26909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26909 raw26909Labels permutation175 permutation2
    _ = mixedMoment B node1032 node1032Labels := by rfl

def raw26910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26910 raw26910Labels = mixedMoment B node2098 node2098Labels := by
  calc
    mixedMoment B raw26910 raw26910Labels = mixedMoment B raw26910step0 raw26910step0Labels := by
      have ha : raw26910step0 = (fun i j => raw26910 (permutation175 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26910step0 raw26910; decide +kernel
      have hl : raw26910step0Labels = raw26910Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26910 raw26910Labels permutation175 permutation2
    _ = mixedMoment B node2098 node2098Labels := by rfl

def raw26911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw26911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26911 raw26911Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw26911 raw26911Labels = mixedMoment B raw26911step0 raw26911step0Labels := by
      have ha : raw26911step0 = (fun i j => raw26911 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26911step0 raw26911; decide +kernel
      have hl : raw26911step0Labels = raw26911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26911 raw26911Labels permutation157 permutation2
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw26912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw26912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26912 raw26912Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw26912 raw26912Labels = mixedMoment B raw26912step0 raw26912step0Labels := by
      have ha : raw26912step0 = (fun i j => raw26912 (permutation163 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26912step0 raw26912; decide +kernel
      have hl : raw26912step0Labels = raw26912Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26912 raw26912Labels permutation163 permutation2
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw26913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1]]
def raw26913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw26913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26913 raw26913Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw26913 raw26913Labels = mixedMoment B raw26913step0 raw26913step0Labels := by
      have hz : ∀ j, raw26913 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26913step0 = (fun i j => raw26913 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26913step0 raw26913; decide +kernel
      have hl : raw26913step0Labels = raw26913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26913 raw26913Labels permutation520 hz
    mixedMoment B raw26913step0 raw26913step0Labels = mixedMoment B raw26913step1 raw26913step1Labels := by
      have ha : raw26913step1 = (fun i j => raw26913step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26913step1 raw26913step0; decide +kernel
      have hl : raw26913step1Labels = raw26913step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26913step0 raw26913step0Labels permutation37 permutation2
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw26914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1]]
def raw26914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26914 raw26914Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw26914 raw26914Labels = mixedMoment B raw26914step0 raw26914step0Labels := by
      have ha : raw26914step0 = (fun i j => raw26914 (permutation251 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26914step0 raw26914; decide +kernel
      have hl : raw26914step0Labels = raw26914Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26914 raw26914Labels permutation251 permutation2
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw26915 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![1, -1], ![0, 0], ![-1, 1]]
def raw26915Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26915step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![1, -1], ![-1, 1]]
def raw26915step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26915step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26915step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26915 raw26915Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw26915 raw26915Labels = mixedMoment B raw26915step0 raw26915step0Labels := by
      have hz : ∀ j, raw26915 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26915step0 = (fun i j => raw26915 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26915step0 raw26915; decide +kernel
      have hl : raw26915step0Labels = raw26915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26915 raw26915Labels permutation520 hz
    mixedMoment B raw26915step0 raw26915step0Labels = mixedMoment B raw26915step1 raw26915step1Labels := by
      have ha : raw26915step1 = (fun i j => raw26915step0 (permutation51 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26915step1 raw26915step0; decide +kernel
      have hl : raw26915step1Labels = raw26915step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26915step0 raw26915step0Labels permutation51 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw26916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26916 raw26916Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw26916 raw26916Labels = mixedMoment B raw26916step0 raw26916step0Labels := by
      have ha : raw26916step0 = (fun i j => raw26916 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26916step0 raw26916; decide +kernel
      have hl : raw26916step0Labels = raw26916Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26916 raw26916Labels permutation170 permutation2
    _ = mixedMoment B node2100 node2100Labels := by rfl

def raw26917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26917 raw26917Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw26917 raw26917Labels = mixedMoment B raw26917step0 raw26917step0Labels := by
      have ha : raw26917step0 = (fun i j => raw26917 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26917step0 raw26917; decide +kernel
      have hl : raw26917step0Labels = raw26917Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26917 raw26917Labels permutation162 permutation2
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw26918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26918 raw26918Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw26918 raw26918Labels = mixedMoment B raw26918step0 raw26918step0Labels := by
      have ha : raw26918step0 = (fun i j => raw26918 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26918step0 raw26918; decide +kernel
      have hl : raw26918step0Labels = raw26918Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26918 raw26918Labels permutation168 permutation2
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw26919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26919 raw26919Labels = mixedMoment B node2204 node2204Labels := by
  calc
    mixedMoment B raw26919 raw26919Labels = mixedMoment B raw26919step0 raw26919step0Labels := by
      have ha : raw26919step0 = (fun i j => raw26919 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26919step0 raw26919; decide +kernel
      have hl : raw26919step0Labels = raw26919Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26919 raw26919Labels permutation246 permutation2
    _ = mixedMoment B node2204 node2204Labels := by rfl

def raw26920 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26920 raw26920Labels = mixedMoment B node1644 node1644Labels := by
  calc
    mixedMoment B raw26920 raw26920Labels = mixedMoment B raw26920step0 raw26920step0Labels := by
      have ha : raw26920step0 = (fun i j => raw26920 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26920step0 raw26920; decide +kernel
      have hl : raw26920step0Labels = raw26920Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26920 raw26920Labels permutation246 permutation4
    mixedMoment B raw26920step0 raw26920step0Labels = mixedMoment B raw26920step1 raw26920step1Labels := by
      have ha : raw26920step1 = -raw26920step0 := by apply Matrix.ext; change ∀ i j, raw26920step1 i j = -(raw26920step0 i j); unfold raw26920step1 raw26920step0; decide +kernel
      have hl : raw26920step1Labels = raw26920step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1644 node1644Labels := by rfl

def raw26921 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw26921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26921step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26921 raw26921Labels = mixedMoment B node736 node736Labels := by
  calc
    mixedMoment B raw26921 raw26921Labels = mixedMoment B raw26921step0 raw26921step0Labels := by
      have ha : raw26921step0 = (fun i j => raw26921 (permutation255 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26921step0 raw26921; decide +kernel
      have hl : raw26921step0Labels = raw26921Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26921 raw26921Labels permutation255 permutation4
    mixedMoment B raw26921step0 raw26921step0Labels = mixedMoment B raw26921step1 raw26921step1Labels := by
      have ha : raw26921step1 = -raw26921step0 := by apply Matrix.ext; change ∀ i j, raw26921step1 i j = -(raw26921step0 i j); unfold raw26921step1 raw26921step0; decide +kernel
      have hl : raw26921step1Labels = raw26921step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node736 node736Labels := by rfl

def raw26922 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26922 raw26922Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw26922 raw26922Labels = mixedMoment B raw26922step0 raw26922step0Labels := by
      have ha : raw26922step0 = (fun i j => raw26922 (permutation249 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26922step0 raw26922; decide +kernel
      have hl : raw26922step0Labels = raw26922Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26922 raw26922Labels permutation249 permutation4
    mixedMoment B raw26922step0 raw26922step0Labels = mixedMoment B raw26922step1 raw26922step1Labels := by
      have ha : raw26922step1 = -raw26922step0 := by apply Matrix.ext; change ∀ i j, raw26922step1 i j = -(raw26922step0 i j); unfold raw26922step1 raw26922step0; decide +kernel
      have hl : raw26922step1Labels = raw26922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node732 node732Labels := by rfl

def raw26923 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26923step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26923 raw26923Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw26923 raw26923Labels = mixedMoment B raw26923step0 raw26923step0Labels := by
      have ha : raw26923step0 = (fun i j => raw26923 (permutation247 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26923step0 raw26923; decide +kernel
      have hl : raw26923step0Labels = raw26923Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26923 raw26923Labels permutation247 permutation4
    mixedMoment B raw26923step0 raw26923step0Labels = mixedMoment B raw26923step1 raw26923step1Labels := by
      have ha : raw26923step1 = -raw26923step0 := by apply Matrix.ext; change ∀ i j, raw26923step1 i j = -(raw26923step0 i j); unfold raw26923step1 raw26923step0; decide +kernel
      have hl : raw26923step1Labels = raw26923step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node732 node732Labels := by rfl

def raw26924 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw26924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26924 raw26924Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw26924 raw26924Labels = mixedMoment B raw26924step0 raw26924step0Labels := by
      have ha : raw26924step0 = (fun i j => raw26924 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26924step0 raw26924; decide +kernel
      have hl : raw26924step0Labels = raw26924Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26924 raw26924Labels permutation246 permutation4
    mixedMoment B raw26924step0 raw26924step0Labels = mixedMoment B raw26924step1 raw26924step1Labels := by
      have ha : raw26924step1 = -raw26924step0 := by apply Matrix.ext; change ∀ i j, raw26924step1 i j = -(raw26924step0 i j); unfold raw26924step1 raw26924step0; decide +kernel
      have hl : raw26924step1Labels = raw26924step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node732 node732Labels := by rfl

def raw26925 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26925 raw26925Labels = mixedMoment B node805 node805Labels := by
  calc
    mixedMoment B raw26925 raw26925Labels = mixedMoment B raw26925step0 raw26925step0Labels := by
      have ha : raw26925step0 = (fun i j => raw26925 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26925step0 raw26925; decide +kernel
      have hl : raw26925step0Labels = raw26925Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26925 raw26925Labels permutation246 permutation4
    mixedMoment B raw26925step0 raw26925step0Labels = mixedMoment B raw26925step1 raw26925step1Labels := by
      have ha : raw26925step1 = -raw26925step0 := by apply Matrix.ext; change ∀ i j, raw26925step1 i j = -(raw26925step0 i j); unfold raw26925step1 raw26925step0; decide +kernel
      have hl : raw26925step1Labels = raw26925step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node805 node805Labels := by rfl

def raw26926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26926 raw26926Labels = mixedMoment B node4171 node4171Labels := by
  calc
    mixedMoment B raw26926 raw26926Labels = mixedMoment B raw26926step0 raw26926step0Labels := by
      have ha : raw26926step0 = (fun i j => raw26926 (permutation240 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26926step0 raw26926; decide +kernel
      have hl : raw26926step0Labels = raw26926Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26926 raw26926Labels permutation240 permutation2
    _ = mixedMoment B node4171 node4171Labels := by rfl

def raw26927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26927 raw26927Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw26927 raw26927Labels = mixedMoment B raw26927step0 raw26927step0Labels := by
      have ha : raw26927step0 = (fun i j => raw26927 (permutation216 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26927step0 raw26927; decide +kernel
      have hl : raw26927step0Labels = raw26927Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26927 raw26927Labels permutation216 permutation2
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw26928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26928 raw26928Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26928 raw26928Labels = mixedMoment B raw26928step0 raw26928step0Labels := by
      have hz : ∀ j, raw26928 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26928step0 = (fun i j => raw26928 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26928step0 raw26928; decide +kernel
      have hl : raw26928step0Labels = raw26928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26928 raw26928Labels permutation520 hz
    mixedMoment B raw26928step0 raw26928step0Labels = mixedMoment B raw26928step1 raw26928step1Labels := by
      have ha : raw26928step1 = (fun i j => raw26928step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26928step1 raw26928step0; decide +kernel
      have hl : raw26928step1Labels = raw26928step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26928step0 raw26928step0Labels permutation50 permutation2
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw26929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26929 raw26929Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26929 raw26929Labels = mixedMoment B raw26929step0 raw26929step0Labels := by
      have hz : ∀ j, raw26929 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26929step0 = (fun i j => raw26929 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26929step0 raw26929; decide +kernel
      have hl : raw26929step0Labels = raw26929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26929 raw26929Labels permutation590 hz
    mixedMoment B raw26929step0 raw26929step0Labels = mixedMoment B raw26929step1 raw26929step1Labels := by
      have ha : raw26929step1 = (fun i j => raw26929step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26929step1 raw26929step0; decide +kernel
      have hl : raw26929step1Labels = raw26929step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26929step0 raw26929step0Labels permutation50 permutation2
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw26930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26930 raw26930Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw26930 raw26930Labels = mixedMoment B raw26930step0 raw26930step0Labels := by
      have ha : raw26930step0 = (fun i j => raw26930 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26930step0 raw26930; decide +kernel
      have hl : raw26930step0Labels = raw26930Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26930 raw26930Labels permutation169 permutation2
    _ = mixedMoment B node4150 node4150Labels := by rfl

def raw26931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26931 raw26931Labels = mixedMoment B node4364 node4364Labels := by
  calc
    mixedMoment B raw26931 raw26931Labels = mixedMoment B raw26931step0 raw26931step0Labels := by
      have ha : raw26931step0 = (fun i j => raw26931 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26931step0 raw26931; decide +kernel
      have hl : raw26931step0Labels = raw26931Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26931 raw26931Labels permutation169 permutation2
    _ = mixedMoment B node4364 node4364Labels := by rfl

def raw26932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26932 raw26932Labels = mixedMoment B node4438 node4438Labels := by
  calc
    mixedMoment B raw26932 raw26932Labels = mixedMoment B raw26932step0 raw26932step0Labels := by
      have ha : raw26932step0 = (fun i j => raw26932 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26932step0 raw26932; decide +kernel
      have hl : raw26932step0Labels = raw26932Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26932 raw26932Labels permutation161 permutation2
    _ = mixedMoment B node4438 node4438Labels := by rfl

def raw26933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26933 raw26933Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw26933 raw26933Labels = mixedMoment B raw26933step0 raw26933step0Labels := by
      have hz : ∀ j, raw26933 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26933step0 = (fun i j => raw26933 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26933step0 raw26933; decide +kernel
      have hl : raw26933step0Labels = raw26933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26933 raw26933Labels permutation520 hz
    mixedMoment B raw26933step0 raw26933step0Labels = mixedMoment B raw26933step1 raw26933step1Labels := by
      have ha : raw26933step1 = (fun i j => raw26933step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26933step1 raw26933step0; decide +kernel
      have hl : raw26933step1Labels = raw26933step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26933step0 raw26933step0Labels permutation37 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw26934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26934 raw26934Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw26934 raw26934Labels = mixedMoment B raw26934step0 raw26934step0Labels := by
      have hz : ∀ j, raw26934 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26934step0 = (fun i j => raw26934 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26934step0 raw26934; decide +kernel
      have hl : raw26934step0Labels = raw26934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26934 raw26934Labels permutation590 hz
    mixedMoment B raw26934step0 raw26934step0Labels = mixedMoment B raw26934step1 raw26934step1Labels := by
      have ha : raw26934step1 = (fun i j => raw26934step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26934step1 raw26934step0; decide +kernel
      have hl : raw26934step1Labels = raw26934step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26934step0 raw26934step0Labels permutation37 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw26935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26935 raw26935Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw26935 raw26935Labels = mixedMoment B raw26935step0 raw26935step0Labels := by
      have ha : raw26935step0 = (fun i j => raw26935 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26935step0 raw26935; decide +kernel
      have hl : raw26935step0Labels = raw26935Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26935 raw26935Labels permutation168 permutation2
    _ = mixedMoment B node4150 node4150Labels := by rfl

def raw26936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26936 raw26936Labels = mixedMoment B node4364 node4364Labels := by
  calc
    mixedMoment B raw26936 raw26936Labels = mixedMoment B raw26936step0 raw26936step0Labels := by
      have ha : raw26936step0 = (fun i j => raw26936 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26936step0 raw26936; decide +kernel
      have hl : raw26936step0Labels = raw26936Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26936 raw26936Labels permutation168 permutation2
    _ = mixedMoment B node4364 node4364Labels := by rfl

def raw26937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26937 raw26937Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw26937 raw26937Labels = mixedMoment B raw26937step0 raw26937step0Labels := by
      have hz : ∀ j, raw26937 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26937step0 = (fun i j => raw26937 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26937step0 raw26937; decide +kernel
      have hl : raw26937step0Labels = raw26937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26937 raw26937Labels permutation520 hz
    mixedMoment B raw26937step0 raw26937step0Labels = mixedMoment B raw26937step1 raw26937step1Labels := by
      have ha : raw26937step1 = (fun i j => raw26937step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26937step1 raw26937step0; decide +kernel
      have hl : raw26937step1Labels = raw26937step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26937step0 raw26937step0Labels permutation36 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw26938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26938 raw26938Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw26938 raw26938Labels = mixedMoment B raw26938step0 raw26938step0Labels := by
      have hz : ∀ j, raw26938 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26938step0 = (fun i j => raw26938 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26938step0 raw26938; decide +kernel
      have hl : raw26938step0Labels = raw26938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26938 raw26938Labels permutation590 hz
    mixedMoment B raw26938step0 raw26938step0Labels = mixedMoment B raw26938step1 raw26938step1Labels := by
      have ha : raw26938step1 = (fun i j => raw26938step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26938step1 raw26938step0; decide +kernel
      have hl : raw26938step1Labels = raw26938step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26938step0 raw26938step0Labels permutation36 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw26939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw26939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26939 raw26939Labels = mixedMoment B node4152 node4152Labels := by
  calc
    mixedMoment B raw26939 raw26939Labels = mixedMoment B raw26939step0 raw26939step0Labels := by
      have ha : raw26939step0 = (fun i j => raw26939 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26939step0 raw26939; decide +kernel
      have hl : raw26939step0Labels = raw26939Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26939 raw26939Labels permutation170 permutation2
    _ = mixedMoment B node4152 node4152Labels := by rfl

def raw26940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw26940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26940 raw26940Labels = mixedMoment B node4366 node4366Labels := by
  calc
    mixedMoment B raw26940 raw26940Labels = mixedMoment B raw26940step0 raw26940step0Labels := by
      have ha : raw26940step0 = (fun i j => raw26940 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26940step0 raw26940; decide +kernel
      have hl : raw26940step0Labels = raw26940Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26940 raw26940Labels permutation170 permutation2
    _ = mixedMoment B node4366 node4366Labels := by rfl

def raw26941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw26941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw26941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26941 raw26941Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw26941 raw26941Labels = mixedMoment B raw26941step0 raw26941step0Labels := by
      have ha : raw26941step0 = (fun i j => raw26941 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26941step0 raw26941; decide +kernel
      have hl : raw26941step0Labels = raw26941Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26941 raw26941Labels permutation162 permutation2
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw26942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw26942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26942 raw26942Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw26942 raw26942Labels = mixedMoment B raw26942step0 raw26942step0Labels := by
      have hz : ∀ j, raw26942 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26942step0 = (fun i j => raw26942 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26942step0 raw26942; decide +kernel
      have hl : raw26942step0Labels = raw26942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26942 raw26942Labels permutation590 hz
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw26943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw26943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26943 raw26943Labels = mixedMoment B node4152 node4152Labels := by
  calc
    mixedMoment B raw26943 raw26943Labels = mixedMoment B raw26943step0 raw26943step0Labels := by
      have ha : raw26943step0 = (fun i j => raw26943 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26943step0 raw26943; decide +kernel
      have hl : raw26943step0Labels = raw26943Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26943 raw26943Labels permutation164 permutation2
    _ = mixedMoment B node4152 node4152Labels := by rfl

def raw26944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw26944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26944 raw26944Labels = mixedMoment B node4366 node4366Labels := by
  calc
    mixedMoment B raw26944 raw26944Labels = mixedMoment B raw26944step0 raw26944step0Labels := by
      have ha : raw26944step0 = (fun i j => raw26944 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26944step0 raw26944; decide +kernel
      have hl : raw26944step0Labels = raw26944Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26944 raw26944Labels permutation164 permutation2
    _ = mixedMoment B node4366 node4366Labels := by rfl

def raw26945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw26945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26945 raw26945Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw26945 raw26945Labels = mixedMoment B raw26945step0 raw26945step0Labels := by
      have hz : ∀ j, raw26945 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26945step0 = (fun i j => raw26945 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26945step0 raw26945; decide +kernel
      have hl : raw26945step0Labels = raw26945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26945 raw26945Labels permutation520 hz
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw26946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26946 raw26946Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw26946 raw26946Labels = mixedMoment B raw26946step0 raw26946step0Labels := by
      have ha : raw26946step0 = (fun i j => raw26946 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26946step0 raw26946; decide +kernel
      have hl : raw26946step0Labels = raw26946Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26946 raw26946Labels permutation240 permutation7
    mixedMoment B raw26946step0 raw26946step0Labels = mixedMoment B raw26946step1 raw26946step1Labels := by
      have ha : raw26946step1 = -raw26946step0 := by apply Matrix.ext; change ∀ i j, raw26946step1 i j = -(raw26946step0 i j); unfold raw26946step1 raw26946step0; decide +kernel
      have hl : raw26946step1Labels = raw26946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26946step1 raw26946step1Labels = mixedMoment B raw26946step2 raw26946step2Labels := by
      have ha : raw26946step2 = raw26946step1 := by apply Matrix.ext; unfold raw26946step2 raw26946step1; decide +kernel
      have hl : raw26946step1Labels = labelEmbedding1 ∘ raw26946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26946step1 raw26946step1Labels raw26946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1506 node1506Labels := by rfl

def raw26947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26947step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26947step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26947 raw26947Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26947 raw26947Labels = mixedMoment B raw26947step0 raw26947step0Labels := by
      have ha : raw26947step0 = (fun i j => raw26947 (permutation244 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26947step0 raw26947; decide +kernel
      have hl : raw26947step0Labels = raw26947Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26947 raw26947Labels permutation244 permutation7
    mixedMoment B raw26947step0 raw26947step0Labels = mixedMoment B raw26947step1 raw26947step1Labels := by
      have ha : raw26947step1 = -raw26947step0 := by apply Matrix.ext; change ∀ i j, raw26947step1 i j = -(raw26947step0 i j); unfold raw26947step1 raw26947step0; decide +kernel
      have hl : raw26947step1Labels = raw26947step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26947step1 raw26947step1Labels = mixedMoment B raw26947step2 raw26947step2Labels := by
      have ha : raw26947step2 = raw26947step1 := by apply Matrix.ext; unfold raw26947step2 raw26947step1; decide +kernel
      have hl : raw26947step1Labels = labelEmbedding1 ∘ raw26947step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26947step1 raw26947step1Labels raw26947step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw26948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26948step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26948step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26948step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26948 raw26948Labels = mixedMoment B node1726 node1726Labels := by
  calc
    mixedMoment B raw26948 raw26948Labels = mixedMoment B raw26948step0 raw26948step0Labels := by
      have hz : ∀ j, raw26948 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26948step0 = (fun i j => raw26948 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26948step0 raw26948; decide +kernel
      have hl : raw26948step0Labels = raw26948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26948 raw26948Labels permutation520 hz
    mixedMoment B raw26948step0 raw26948step0Labels = mixedMoment B raw26948step1 raw26948step1Labels := by
      have ha : raw26948step1 = (fun i j => raw26948step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26948step1 raw26948step0; decide +kernel
      have hl : raw26948step1Labels = raw26948step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26948step0 raw26948step0Labels permutation50 permutation7
    mixedMoment B raw26948step1 raw26948step1Labels = mixedMoment B raw26948step2 raw26948step2Labels := by
      have ha : raw26948step2 = -raw26948step1 := by apply Matrix.ext; change ∀ i j, raw26948step2 i j = -(raw26948step1 i j); unfold raw26948step2 raw26948step1; decide +kernel
      have hl : raw26948step2Labels = raw26948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26948step2 raw26948step2Labels = mixedMoment B raw26948step3 raw26948step3Labels := by
      have ha : raw26948step3 = raw26948step2 := by apply Matrix.ext; unfold raw26948step3 raw26948step2; decide +kernel
      have hl : raw26948step2Labels = labelEmbedding1 ∘ raw26948step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26948step2 raw26948step2Labels raw26948step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1726 node1726Labels := by rfl

def raw26949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26949step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26949step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26949step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26949step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26949 raw26949Labels = mixedMoment B node1726 node1726Labels := by
  calc
    mixedMoment B raw26949 raw26949Labels = mixedMoment B raw26949step0 raw26949step0Labels := by
      have hz : ∀ j, raw26949 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26949step0 = (fun i j => raw26949 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26949step0 raw26949; decide +kernel
      have hl : raw26949step0Labels = raw26949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26949 raw26949Labels permutation590 hz
    mixedMoment B raw26949step0 raw26949step0Labels = mixedMoment B raw26949step1 raw26949step1Labels := by
      have ha : raw26949step1 = (fun i j => raw26949step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26949step1 raw26949step0; decide +kernel
      have hl : raw26949step1Labels = raw26949step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26949step0 raw26949step0Labels permutation50 permutation7
    mixedMoment B raw26949step1 raw26949step1Labels = mixedMoment B raw26949step2 raw26949step2Labels := by
      have ha : raw26949step2 = -raw26949step1 := by apply Matrix.ext; change ∀ i j, raw26949step2 i j = -(raw26949step1 i j); unfold raw26949step2 raw26949step1; decide +kernel
      have hl : raw26949step2Labels = raw26949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26949step2 raw26949step2Labels = mixedMoment B raw26949step3 raw26949step3Labels := by
      have ha : raw26949step3 = raw26949step2 := by apply Matrix.ext; unfold raw26949step3 raw26949step2; decide +kernel
      have hl : raw26949step2Labels = labelEmbedding1 ∘ raw26949step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26949step2 raw26949step2Labels raw26949step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1726 node1726Labels := by rfl

def raw26950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26950 raw26950Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw26950 raw26950Labels = mixedMoment B raw26950step0 raw26950step0Labels := by
      have ha : raw26950step0 = (fun i j => raw26950 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26950step0 raw26950; decide +kernel
      have hl : raw26950step0Labels = raw26950Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26950 raw26950Labels permutation241 permutation7
    mixedMoment B raw26950step0 raw26950step0Labels = mixedMoment B raw26950step1 raw26950step1Labels := by
      have ha : raw26950step1 = -raw26950step0 := by apply Matrix.ext; change ∀ i j, raw26950step1 i j = -(raw26950step0 i j); unfold raw26950step1 raw26950step0; decide +kernel
      have hl : raw26950step1Labels = raw26950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26950step1 raw26950step1Labels = mixedMoment B raw26950step2 raw26950step2Labels := by
      have ha : raw26950step2 = raw26950step1 := by apply Matrix.ext; unfold raw26950step2 raw26950step1; decide +kernel
      have hl : raw26950step1Labels = labelEmbedding1 ∘ raw26950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26950step1 raw26950step1Labels raw26950step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

def raw26951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26951step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26951step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26951step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26951 raw26951Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw26951 raw26951Labels = mixedMoment B raw26951step0 raw26951step0Labels := by
      have ha : raw26951step0 = (fun i j => raw26951 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26951step0 raw26951; decide +kernel
      have hl : raw26951step0Labels = raw26951Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26951 raw26951Labels permutation241 permutation7
    mixedMoment B raw26951step0 raw26951step0Labels = mixedMoment B raw26951step1 raw26951step1Labels := by
      have ha : raw26951step1 = -raw26951step0 := by apply Matrix.ext; change ∀ i j, raw26951step1 i j = -(raw26951step0 i j); unfold raw26951step1 raw26951step0; decide +kernel
      have hl : raw26951step1Labels = raw26951step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26951step1 raw26951step1Labels = mixedMoment B raw26951step2 raw26951step2Labels := by
      have ha : raw26951step2 = raw26951step1 := by apply Matrix.ext; unfold raw26951step2 raw26951step1; decide +kernel
      have hl : raw26951step1Labels = labelEmbedding1 ∘ raw26951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26951step1 raw26951step1Labels raw26951step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

def raw26952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw26952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26952step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26952 raw26952Labels = mixedMoment B node1705 node1705Labels := by
  calc
    mixedMoment B raw26952 raw26952Labels = mixedMoment B raw26952step0 raw26952step0Labels := by
      have ha : raw26952step0 = (fun i j => raw26952 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26952step0 raw26952; decide +kernel
      have hl : raw26952step0Labels = raw26952Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26952 raw26952Labels permutation241 permutation7
    mixedMoment B raw26952step0 raw26952step0Labels = mixedMoment B raw26952step1 raw26952step1Labels := by
      have ha : raw26952step1 = -raw26952step0 := by apply Matrix.ext; change ∀ i j, raw26952step1 i j = -(raw26952step0 i j); unfold raw26952step1 raw26952step0; decide +kernel
      have hl : raw26952step1Labels = raw26952step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26952step1 raw26952step1Labels = mixedMoment B raw26952step2 raw26952step2Labels := by
      have ha : raw26952step2 = raw26952step1 := by apply Matrix.ext; unfold raw26952step2 raw26952step1; decide +kernel
      have hl : raw26952step1Labels = labelEmbedding1 ∘ raw26952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26952step1 raw26952step1Labels raw26952step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1705 node1705Labels := by rfl

def raw26953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26953step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26953step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26953step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26953 raw26953Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw26953 raw26953Labels = mixedMoment B raw26953step0 raw26953step0Labels := by
      have hz : ∀ j, raw26953 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26953step0 = (fun i j => raw26953 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26953step0 raw26953; decide +kernel
      have hl : raw26953step0Labels = raw26953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26953 raw26953Labels permutation520 hz
    mixedMoment B raw26953step0 raw26953step0Labels = mixedMoment B raw26953step1 raw26953step1Labels := by
      have ha : raw26953step1 = (fun i j => raw26953step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26953step1 raw26953step0; decide +kernel
      have hl : raw26953step1Labels = raw26953step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26953step0 raw26953step0Labels permutation51 permutation7
    mixedMoment B raw26953step1 raw26953step1Labels = mixedMoment B raw26953step2 raw26953step2Labels := by
      have ha : raw26953step2 = -raw26953step1 := by apply Matrix.ext; change ∀ i j, raw26953step2 i j = -(raw26953step1 i j); unfold raw26953step2 raw26953step1; decide +kernel
      have hl : raw26953step2Labels = raw26953step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26953step2 raw26953step2Labels = mixedMoment B raw26953step3 raw26953step3Labels := by
      have ha : raw26953step3 = raw26953step2 := by apply Matrix.ext; unfold raw26953step3 raw26953step2; decide +kernel
      have hl : raw26953step2Labels = labelEmbedding1 ∘ raw26953step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26953step2 raw26953step2Labels raw26953step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw26954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26954step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26954step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26954step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26954step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26954 raw26954Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw26954 raw26954Labels = mixedMoment B raw26954step0 raw26954step0Labels := by
      have hz : ∀ j, raw26954 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26954step0 = (fun i j => raw26954 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26954step0 raw26954; decide +kernel
      have hl : raw26954step0Labels = raw26954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26954 raw26954Labels permutation590 hz
    mixedMoment B raw26954step0 raw26954step0Labels = mixedMoment B raw26954step1 raw26954step1Labels := by
      have ha : raw26954step1 = (fun i j => raw26954step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26954step1 raw26954step0; decide +kernel
      have hl : raw26954step1Labels = raw26954step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26954step0 raw26954step0Labels permutation51 permutation7
    mixedMoment B raw26954step1 raw26954step1Labels = mixedMoment B raw26954step2 raw26954step2Labels := by
      have ha : raw26954step2 = -raw26954step1 := by apply Matrix.ext; change ∀ i j, raw26954step2 i j = -(raw26954step1 i j); unfold raw26954step2 raw26954step1; decide +kernel
      have hl : raw26954step2Labels = raw26954step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26954step2 raw26954step2Labels = mixedMoment B raw26954step3 raw26954step3Labels := by
      have ha : raw26954step3 = raw26954step2 := by apply Matrix.ext; unfold raw26954step3 raw26954step2; decide +kernel
      have hl : raw26954step2Labels = labelEmbedding1 ∘ raw26954step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26954step2 raw26954step2Labels raw26954step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw26955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26955step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26955 raw26955Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw26955 raw26955Labels = mixedMoment B raw26955step0 raw26955step0Labels := by
      have ha : raw26955step0 = (fun i j => raw26955 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26955step0 raw26955; decide +kernel
      have hl : raw26955step0Labels = raw26955Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26955 raw26955Labels permutation240 permutation7
    mixedMoment B raw26955step0 raw26955step0Labels = mixedMoment B raw26955step1 raw26955step1Labels := by
      have ha : raw26955step1 = -raw26955step0 := by apply Matrix.ext; change ∀ i j, raw26955step1 i j = -(raw26955step0 i j); unfold raw26955step1 raw26955step0; decide +kernel
      have hl : raw26955step1Labels = raw26955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26955step1 raw26955step1Labels = mixedMoment B raw26955step2 raw26955step2Labels := by
      have ha : raw26955step2 = raw26955step1 := by apply Matrix.ext; unfold raw26955step2 raw26955step1; decide +kernel
      have hl : raw26955step1Labels = labelEmbedding1 ∘ raw26955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26955step1 raw26955step1Labels raw26955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

def raw26956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26956step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26956step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26956 raw26956Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw26956 raw26956Labels = mixedMoment B raw26956step0 raw26956step0Labels := by
      have ha : raw26956step0 = (fun i j => raw26956 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26956step0 raw26956; decide +kernel
      have hl : raw26956step0Labels = raw26956Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26956 raw26956Labels permutation240 permutation7
    mixedMoment B raw26956step0 raw26956step0Labels = mixedMoment B raw26956step1 raw26956step1Labels := by
      have ha : raw26956step1 = -raw26956step0 := by apply Matrix.ext; change ∀ i j, raw26956step1 i j = -(raw26956step0 i j); unfold raw26956step1 raw26956step0; decide +kernel
      have hl : raw26956step1Labels = raw26956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26956step1 raw26956step1Labels = mixedMoment B raw26956step2 raw26956step2Labels := by
      have ha : raw26956step2 = raw26956step1 := by apply Matrix.ext; unfold raw26956step2 raw26956step1; decide +kernel
      have hl : raw26956step1Labels = labelEmbedding1 ∘ raw26956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26956step1 raw26956step1Labels raw26956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

def raw26957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26957step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26957step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26957step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26957step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26957 raw26957Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw26957 raw26957Labels = mixedMoment B raw26957step0 raw26957step0Labels := by
      have hz : ∀ j, raw26957 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26957step0 = (fun i j => raw26957 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26957step0 raw26957; decide +kernel
      have hl : raw26957step0Labels = raw26957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26957 raw26957Labels permutation520 hz
    mixedMoment B raw26957step0 raw26957step0Labels = mixedMoment B raw26957step1 raw26957step1Labels := by
      have ha : raw26957step1 = (fun i j => raw26957step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26957step1 raw26957step0; decide +kernel
      have hl : raw26957step1Labels = raw26957step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26957step0 raw26957step0Labels permutation50 permutation7
    mixedMoment B raw26957step1 raw26957step1Labels = mixedMoment B raw26957step2 raw26957step2Labels := by
      have ha : raw26957step2 = -raw26957step1 := by apply Matrix.ext; change ∀ i j, raw26957step2 i j = -(raw26957step1 i j); unfold raw26957step2 raw26957step1; decide +kernel
      have hl : raw26957step2Labels = raw26957step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26957step2 raw26957step2Labels = mixedMoment B raw26957step3 raw26957step3Labels := by
      have ha : raw26957step3 = raw26957step2 := by apply Matrix.ext; unfold raw26957step3 raw26957step2; decide +kernel
      have hl : raw26957step2Labels = labelEmbedding1 ∘ raw26957step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26957step2 raw26957step2Labels raw26957step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw26958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26958step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26958step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26958 raw26958Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw26958 raw26958Labels = mixedMoment B raw26958step0 raw26958step0Labels := by
      have hz : ∀ j, raw26958 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26958step0 = (fun i j => raw26958 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26958step0 raw26958; decide +kernel
      have hl : raw26958step0Labels = raw26958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26958 raw26958Labels permutation590 hz
    mixedMoment B raw26958step0 raw26958step0Labels = mixedMoment B raw26958step1 raw26958step1Labels := by
      have ha : raw26958step1 = (fun i j => raw26958step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26958step1 raw26958step0; decide +kernel
      have hl : raw26958step1Labels = raw26958step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26958step0 raw26958step0Labels permutation50 permutation7
    mixedMoment B raw26958step1 raw26958step1Labels = mixedMoment B raw26958step2 raw26958step2Labels := by
      have ha : raw26958step2 = -raw26958step1 := by apply Matrix.ext; change ∀ i j, raw26958step2 i j = -(raw26958step1 i j); unfold raw26958step2 raw26958step1; decide +kernel
      have hl : raw26958step2Labels = raw26958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26958step2 raw26958step2Labels = mixedMoment B raw26958step3 raw26958step3Labels := by
      have ha : raw26958step3 = raw26958step2 := by apply Matrix.ext; unfold raw26958step3 raw26958step2; decide +kernel
      have hl : raw26958step2Labels = labelEmbedding1 ∘ raw26958step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26958step2 raw26958step2Labels raw26958step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw26959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw26959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26959 raw26959Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw26959 raw26959Labels = mixedMoment B raw26959step0 raw26959step0Labels := by
      have ha : raw26959step0 = (fun i j => raw26959 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26959step0 raw26959; decide +kernel
      have hl : raw26959step0Labels = raw26959Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26959 raw26959Labels permutation260 permutation7
    mixedMoment B raw26959step0 raw26959step0Labels = mixedMoment B raw26959step1 raw26959step1Labels := by
      have ha : raw26959step1 = -raw26959step0 := by apply Matrix.ext; change ∀ i j, raw26959step1 i j = -(raw26959step0 i j); unfold raw26959step1 raw26959step0; decide +kernel
      have hl : raw26959step1Labels = raw26959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26959step1 raw26959step1Labels = mixedMoment B raw26959step2 raw26959step2Labels := by
      have ha : raw26959step2 = raw26959step1 := by apply Matrix.ext; unfold raw26959step2 raw26959step1; decide +kernel
      have hl : raw26959step1Labels = labelEmbedding1 ∘ raw26959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26959step1 raw26959step1Labels raw26959step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1510 node1510Labels := by rfl

def raw26960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw26960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26960step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26960 raw26960Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw26960 raw26960Labels = mixedMoment B raw26960step0 raw26960step0Labels := by
      have ha : raw26960step0 = (fun i j => raw26960 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26960step0 raw26960; decide +kernel
      have hl : raw26960step0Labels = raw26960Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26960 raw26960Labels permutation260 permutation7
    mixedMoment B raw26960step0 raw26960step0Labels = mixedMoment B raw26960step1 raw26960step1Labels := by
      have ha : raw26960step1 = -raw26960step0 := by apply Matrix.ext; change ∀ i j, raw26960step1 i j = -(raw26960step0 i j); unfold raw26960step1 raw26960step0; decide +kernel
      have hl : raw26960step1Labels = raw26960step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26960step1 raw26960step1Labels = mixedMoment B raw26960step2 raw26960step2Labels := by
      have ha : raw26960step2 = raw26960step1 := by apply Matrix.ext; unfold raw26960step2 raw26960step1; decide +kernel
      have hl : raw26960step1Labels = labelEmbedding1 ∘ raw26960step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26960step1 raw26960step1Labels raw26960step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

def raw26961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw26961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw26961step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26961step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26961 raw26961Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw26961 raw26961Labels = mixedMoment B raw26961step0 raw26961step0Labels := by
      have ha : raw26961step0 = (fun i j => raw26961 (permutation261 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26961step0 raw26961; decide +kernel
      have hl : raw26961step0Labels = raw26961Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26961 raw26961Labels permutation261 permutation7
    mixedMoment B raw26961step0 raw26961step0Labels = mixedMoment B raw26961step1 raw26961step1Labels := by
      have ha : raw26961step1 = -raw26961step0 := by apply Matrix.ext; change ∀ i j, raw26961step1 i j = -(raw26961step0 i j); unfold raw26961step1 raw26961step0; decide +kernel
      have hl : raw26961step1Labels = raw26961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26961step1 raw26961step1Labels = mixedMoment B raw26961step2 raw26961step2Labels := by
      have ha : raw26961step2 = raw26961step1 := by apply Matrix.ext; unfold raw26961step2 raw26961step1; decide +kernel
      have hl : raw26961step1Labels = labelEmbedding1 ∘ raw26961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26961step1 raw26961step1Labels raw26961step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw26962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw26962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26962step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26962 raw26962Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw26962 raw26962Labels = mixedMoment B raw26962step0 raw26962step0Labels := by
      have hz : ∀ j, raw26962 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26962step0 = (fun i j => raw26962 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26962step0 raw26962; decide +kernel
      have hl : raw26962step0Labels = raw26962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26962 raw26962Labels permutation590 hz
    mixedMoment B raw26962step0 raw26962step0Labels = mixedMoment B raw26962step1 raw26962step1Labels := by
      have ha : raw26962step1 = (fun i j => raw26962step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26962step1 raw26962step0; decide +kernel
      have hl : raw26962step1Labels = raw26962step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26962step0 raw26962step0Labels permutation50 permutation7
    mixedMoment B raw26962step1 raw26962step1Labels = mixedMoment B raw26962step2 raw26962step2Labels := by
      have ha : raw26962step2 = -raw26962step1 := by apply Matrix.ext; change ∀ i j, raw26962step2 i j = -(raw26962step1 i j); unfold raw26962step2 raw26962step1; decide +kernel
      have hl : raw26962step2Labels = raw26962step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26962step2 raw26962step2Labels = mixedMoment B raw26962step3 raw26962step3Labels := by
      have ha : raw26962step3 = raw26962step2 := by apply Matrix.ext; unfold raw26962step3 raw26962step2; decide +kernel
      have hl : raw26962step2Labels = labelEmbedding1 ∘ raw26962step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26962step2 raw26962step2Labels raw26962step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw26963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw26963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26963step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26963step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26963step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26963step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26963 raw26963Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw26963 raw26963Labels = mixedMoment B raw26963step0 raw26963step0Labels := by
      have ha : raw26963step0 = (fun i j => raw26963 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26963step0 raw26963; decide +kernel
      have hl : raw26963step0Labels = raw26963Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26963 raw26963Labels permutation240 permutation7
    mixedMoment B raw26963step0 raw26963step0Labels = mixedMoment B raw26963step1 raw26963step1Labels := by
      have ha : raw26963step1 = -raw26963step0 := by apply Matrix.ext; change ∀ i j, raw26963step1 i j = -(raw26963step0 i j); unfold raw26963step1 raw26963step0; decide +kernel
      have hl : raw26963step1Labels = raw26963step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26963step1 raw26963step1Labels = mixedMoment B raw26963step2 raw26963step2Labels := by
      have ha : raw26963step2 = raw26963step1 := by apply Matrix.ext; unfold raw26963step2 raw26963step1; decide +kernel
      have hl : raw26963step1Labels = labelEmbedding1 ∘ raw26963step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26963step1 raw26963step1Labels raw26963step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1510 node1510Labels := by rfl

def raw26964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw26964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26964step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26964 raw26964Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw26964 raw26964Labels = mixedMoment B raw26964step0 raw26964step0Labels := by
      have ha : raw26964step0 = (fun i j => raw26964 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26964step0 raw26964; decide +kernel
      have hl : raw26964step0Labels = raw26964Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26964 raw26964Labels permutation240 permutation7
    mixedMoment B raw26964step0 raw26964step0Labels = mixedMoment B raw26964step1 raw26964step1Labels := by
      have ha : raw26964step1 = -raw26964step0 := by apply Matrix.ext; change ∀ i j, raw26964step1 i j = -(raw26964step0 i j); unfold raw26964step1 raw26964step0; decide +kernel
      have hl : raw26964step1Labels = raw26964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26964step1 raw26964step1Labels = mixedMoment B raw26964step2 raw26964step2Labels := by
      have ha : raw26964step2 = raw26964step1 := by apply Matrix.ext; unfold raw26964step2 raw26964step1; decide +kernel
      have hl : raw26964step1Labels = labelEmbedding1 ∘ raw26964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26964step1 raw26964step1Labels raw26964step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

def raw26965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw26965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26965step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26965step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26965step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26965step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26965 raw26965Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw26965 raw26965Labels = mixedMoment B raw26965step0 raw26965step0Labels := by
      have hz : ∀ j, raw26965 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26965step0 = (fun i j => raw26965 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26965step0 raw26965; decide +kernel
      have hl : raw26965step0Labels = raw26965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26965 raw26965Labels permutation520 hz
    mixedMoment B raw26965step0 raw26965step0Labels = mixedMoment B raw26965step1 raw26965step1Labels := by
      have ha : raw26965step1 = (fun i j => raw26965step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26965step1 raw26965step0; decide +kernel
      have hl : raw26965step1Labels = raw26965step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26965step0 raw26965step0Labels permutation50 permutation7
    mixedMoment B raw26965step1 raw26965step1Labels = mixedMoment B raw26965step2 raw26965step2Labels := by
      have ha : raw26965step2 = -raw26965step1 := by apply Matrix.ext; change ∀ i j, raw26965step2 i j = -(raw26965step1 i j); unfold raw26965step2 raw26965step1; decide +kernel
      have hl : raw26965step2Labels = raw26965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26965step2 raw26965step2Labels = mixedMoment B raw26965step3 raw26965step3Labels := by
      have ha : raw26965step3 = raw26965step2 := by apply Matrix.ext; unfold raw26965step3 raw26965step2; decide +kernel
      have hl : raw26965step2Labels = labelEmbedding1 ∘ raw26965step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26965step2 raw26965step2Labels raw26965step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw26966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26966 raw26966Labels = mixedMoment B node599 node599Labels := by
  calc
    mixedMoment B raw26966 raw26966Labels = mixedMoment B raw26966step0 raw26966step0Labels := by
      have ha : raw26966step0 = (fun i j => raw26966 (permutation240 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26966step0 raw26966; decide +kernel
      have hl : raw26966step0Labels = raw26966Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26966 raw26966Labels permutation240 permutation2
    _ = mixedMoment B node599 node599Labels := by rfl

def raw26967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26967 raw26967Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw26967 raw26967Labels = mixedMoment B raw26967step0 raw26967step0Labels := by
      have ha : raw26967step0 = (fun i j => raw26967 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26967step0 raw26967; decide +kernel
      have hl : raw26967step0Labels = raw26967Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26967 raw26967Labels permutation168 permutation2
    _ = mixedMoment B node1039 node1039Labels := by rfl

def raw26968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26968 raw26968Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw26968 raw26968Labels = mixedMoment B raw26968step0 raw26968step0Labels := by
      have ha : raw26968step0 = (fun i j => raw26968 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26968step0 raw26968; decide +kernel
      have hl : raw26968step0Labels = raw26968Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26968 raw26968Labels permutation192 permutation2
    _ = mixedMoment B node1039 node1039Labels := by rfl

def raw26969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26969 raw26969Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw26969 raw26969Labels = mixedMoment B raw26969step0 raw26969step0Labels := by
      have ha : raw26969step0 = (fun i j => raw26969 (permutation216 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26969step0 raw26969; decide +kernel
      have hl : raw26969step0Labels = raw26969Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26969 raw26969Labels permutation216 permutation2
    _ = mixedMoment B node1039 node1039Labels := by rfl

def raw26970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26970 raw26970Labels = mixedMoment B node1081 node1081Labels := by
  calc
    mixedMoment B raw26970 raw26970Labels = mixedMoment B raw26970step0 raw26970step0Labels := by
      have hz : ∀ j, raw26970 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26970step0 = (fun i j => raw26970 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26970step0 raw26970; decide +kernel
      have hl : raw26970step0Labels = raw26970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26970 raw26970Labels permutation520 hz
    mixedMoment B raw26970step0 raw26970step0Labels = mixedMoment B raw26970step1 raw26970step1Labels := by
      have ha : raw26970step1 = (fun i j => raw26970step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26970step1 raw26970step0; decide +kernel
      have hl : raw26970step1Labels = raw26970step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26970step0 raw26970step0Labels permutation50 permutation2
    _ = mixedMoment B node1081 node1081Labels := by rfl

def raw26971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26971 raw26971Labels = mixedMoment B node1081 node1081Labels := by
  calc
    mixedMoment B raw26971 raw26971Labels = mixedMoment B raw26971step0 raw26971step0Labels := by
      have hz : ∀ j, raw26971 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26971step0 = (fun i j => raw26971 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26971step0 raw26971; decide +kernel
      have hl : raw26971step0Labels = raw26971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26971 raw26971Labels permutation590 hz
    mixedMoment B raw26971step0 raw26971step0Labels = mixedMoment B raw26971step1 raw26971step1Labels := by
      have ha : raw26971step1 = (fun i j => raw26971step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26971step1 raw26971step0; decide +kernel
      have hl : raw26971step1Labels = raw26971step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26971step0 raw26971step0Labels permutation50 permutation2
    _ = mixedMoment B node1081 node1081Labels := by rfl

def raw26972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26972step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26972 raw26972Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw26972 raw26972Labels = mixedMoment B raw26972step0 raw26972step0Labels := by
      have ha : raw26972step0 = (fun i j => raw26972 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26972step0 raw26972; decide +kernel
      have hl : raw26972step0Labels = raw26972Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26972 raw26972Labels permutation168 permutation3
    mixedMoment B raw26972step0 raw26972step0Labels = mixedMoment B raw26972step1 raw26972step1Labels := by
      have ha : raw26972step1 = raw26972step0 := by apply Matrix.ext; unfold raw26972step1 raw26972step0; decide +kernel
      have hl : raw26972step0Labels = labelEmbedding6 ∘ raw26972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26972step0 raw26972step0Labels raw26972step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw26973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26973step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26973step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26973 raw26973Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw26973 raw26973Labels = mixedMoment B raw26973step0 raw26973step0Labels := by
      have hz : ∀ j, raw26973 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26973step0 = (fun i j => raw26973 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26973step0 raw26973; decide +kernel
      have hl : raw26973step0Labels = raw26973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26973 raw26973Labels permutation434 hz
    mixedMoment B raw26973step0 raw26973step0Labels = mixedMoment B raw26973step1 raw26973step1Labels := by
      have ha : raw26973step1 = (fun i j => raw26973step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26973step1 raw26973step0; decide +kernel
      have hl : raw26973step1Labels = raw26973step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26973step0 raw26973step0Labels permutation35 permutation3
    mixedMoment B raw26973step1 raw26973step1Labels = mixedMoment B raw26973step2 raw26973step2Labels := by
      have ha : raw26973step2 = raw26973step1 := by apply Matrix.ext; unfold raw26973step2 raw26973step1; decide +kernel
      have hl : raw26973step1Labels = labelEmbedding6 ∘ raw26973step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26973step1 raw26973step1Labels raw26973step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw26974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26974step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26974 raw26974Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw26974 raw26974Labels = mixedMoment B raw26974step0 raw26974step0Labels := by
      have ha : raw26974step0 = (fun i j => raw26974 (permutation228 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26974step0 raw26974; decide +kernel
      have hl : raw26974step0Labels = raw26974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26974 raw26974Labels permutation228 permutation3
    mixedMoment B raw26974step0 raw26974step0Labels = mixedMoment B raw26974step1 raw26974step1Labels := by
      have ha : raw26974step1 = raw26974step0 := by apply Matrix.ext; unfold raw26974step1 raw26974step0; decide +kernel
      have hl : raw26974step0Labels = labelEmbedding6 ∘ raw26974step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26974step0 raw26974step0Labels raw26974step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw26975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26975step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26975 raw26975Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw26975 raw26975Labels = mixedMoment B raw26975step0 raw26975step0Labels := by
      have ha : raw26975step0 = (fun i j => raw26975 (permutation250 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26975step0 raw26975; decide +kernel
      have hl : raw26975step0Labels = raw26975Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26975 raw26975Labels permutation250 permutation3
    mixedMoment B raw26975step0 raw26975step0Labels = mixedMoment B raw26975step1 raw26975step1Labels := by
      have ha : raw26975step1 = raw26975step0 := by apply Matrix.ext; unfold raw26975step1 raw26975step0; decide +kernel
      have hl : raw26975step0Labels = labelEmbedding6 ∘ raw26975step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26975step0 raw26975step0Labels raw26975step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw26976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26976step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26976 raw26976Labels = mixedMoment B node4113 node4113Labels := by
  calc
    mixedMoment B raw26976 raw26976Labels = mixedMoment B raw26976step0 raw26976step0Labels := by
      have ha : raw26976step0 = (fun i j => raw26976 (permutation243 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26976step0 raw26976; decide +kernel
      have hl : raw26976step0Labels = raw26976Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26976 raw26976Labels permutation243 permutation3
    mixedMoment B raw26976step0 raw26976step0Labels = mixedMoment B raw26976step1 raw26976step1Labels := by
      have ha : raw26976step1 = raw26976step0 := by apply Matrix.ext; unfold raw26976step1 raw26976step0; decide +kernel
      have hl : raw26976step0Labels = labelEmbedding6 ∘ raw26976step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26976step0 raw26976step0Labels raw26976step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4113 node4113Labels := by rfl

def raw26977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26977step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26977step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26977 raw26977Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26977 raw26977Labels = mixedMoment B raw26977step0 raw26977step0Labels := by
      have hz : ∀ j, raw26977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26977step0 = (fun i j => raw26977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26977step0 raw26977; decide +kernel
      have hl : raw26977step0Labels = raw26977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26977 raw26977Labels permutation434 hz
    mixedMoment B raw26977step0 raw26977step0Labels = mixedMoment B raw26977step1 raw26977step1Labels := by
      have ha : raw26977step1 = (fun i j => raw26977step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26977step1 raw26977step0; decide +kernel
      have hl : raw26977step1Labels = raw26977step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26977step0 raw26977step0Labels permutation49 permutation3
    mixedMoment B raw26977step1 raw26977step1Labels = mixedMoment B raw26977step2 raw26977step2Labels := by
      have ha : raw26977step2 = raw26977step1 := by apply Matrix.ext; unfold raw26977step2 raw26977step1; decide +kernel
      have hl : raw26977step1Labels = labelEmbedding6 ∘ raw26977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26977step1 raw26977step1Labels raw26977step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw26978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26978step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26978 raw26978Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw26978 raw26978Labels = mixedMoment B raw26978step0 raw26978step0Labels := by
      have ha : raw26978step0 = (fun i j => raw26978 (permutation243 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26978step0 raw26978; decide +kernel
      have hl : raw26978step0Labels = raw26978Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26978 raw26978Labels permutation243 permutation3
    mixedMoment B raw26978step0 raw26978step0Labels = mixedMoment B raw26978step1 raw26978step1Labels := by
      have ha : raw26978step1 = raw26978step0 := by apply Matrix.ext; unfold raw26978step1 raw26978step0; decide +kernel
      have hl : raw26978step0Labels = labelEmbedding6 ∘ raw26978step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26978step0 raw26978step0Labels raw26978step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw26979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26979step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26979 raw26979Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw26979 raw26979Labels = mixedMoment B raw26979step0 raw26979step0Labels := by
      have ha : raw26979step0 = (fun i j => raw26979 (permutation263 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26979step0 raw26979; decide +kernel
      have hl : raw26979step0Labels = raw26979Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26979 raw26979Labels permutation263 permutation3
    mixedMoment B raw26979step0 raw26979step0Labels = mixedMoment B raw26979step1 raw26979step1Labels := by
      have ha : raw26979step1 = raw26979step0 := by apply Matrix.ext; unfold raw26979step1 raw26979step0; decide +kernel
      have hl : raw26979step0Labels = labelEmbedding6 ∘ raw26979step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26979step0 raw26979step0Labels raw26979step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw26980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26980step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26980step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26980 raw26980Labels = mixedMoment B node4098 node4098Labels := by
  calc
    mixedMoment B raw26980 raw26980Labels = mixedMoment B raw26980step0 raw26980step0Labels := by
      have ha : raw26980step0 = (fun i j => raw26980 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26980step0 raw26980; decide +kernel
      have hl : raw26980step0Labels = raw26980Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26980 raw26980Labels permutation169 permutation3
    mixedMoment B raw26980step0 raw26980step0Labels = mixedMoment B raw26980step1 raw26980step1Labels := by
      have ha : raw26980step1 = raw26980step0 := by apply Matrix.ext; unfold raw26980step1 raw26980step0; decide +kernel
      have hl : raw26980step0Labels = labelEmbedding6 ∘ raw26980step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26980step0 raw26980step0Labels raw26980step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4098 node4098Labels := by rfl

def raw26981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26981step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26981 raw26981Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw26981 raw26981Labels = mixedMoment B raw26981step0 raw26981step0Labels := by
      have ha : raw26981step0 = (fun i j => raw26981 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26981step0 raw26981; decide +kernel
      have hl : raw26981step0Labels = raw26981Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26981 raw26981Labels permutation169 permutation3
    mixedMoment B raw26981step0 raw26981step0Labels = mixedMoment B raw26981step1 raw26981step1Labels := by
      have ha : raw26981step1 = raw26981step0 := by apply Matrix.ext; unfold raw26981step1 raw26981step0; decide +kernel
      have hl : raw26981step0Labels = labelEmbedding6 ∘ raw26981step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26981step0 raw26981step0Labels raw26981step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

def raw26982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26982step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26982step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26982 raw26982Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw26982 raw26982Labels = mixedMoment B raw26982step0 raw26982step0Labels := by
      have hz : ∀ j, raw26982 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26982step0 = (fun i j => raw26982 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26982step0 raw26982; decide +kernel
      have hl : raw26982step0Labels = raw26982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26982 raw26982Labels permutation434 hz
    mixedMoment B raw26982step0 raw26982step0Labels = mixedMoment B raw26982step1 raw26982step1Labels := by
      have ha : raw26982step1 = (fun i j => raw26982step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26982step1 raw26982step0; decide +kernel
      have hl : raw26982step1Labels = raw26982step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26982step0 raw26982step0Labels permutation35 permutation3
    mixedMoment B raw26982step1 raw26982step1Labels = mixedMoment B raw26982step2 raw26982step2Labels := by
      have ha : raw26982step2 = raw26982step1 := by apply Matrix.ext; unfold raw26982step2 raw26982step1; decide +kernel
      have hl : raw26982step1Labels = labelEmbedding6 ∘ raw26982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26982step1 raw26982step1Labels raw26982step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw26983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26983step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26983 raw26983Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw26983 raw26983Labels = mixedMoment B raw26983step0 raw26983step0Labels := by
      have ha : raw26983step0 = (fun i j => raw26983 (permutation229 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26983step0 raw26983; decide +kernel
      have hl : raw26983step0Labels = raw26983Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26983 raw26983Labels permutation229 permutation3
    mixedMoment B raw26983step0 raw26983step0Labels = mixedMoment B raw26983step1 raw26983step1Labels := by
      have ha : raw26983step1 = raw26983step0 := by apply Matrix.ext; unfold raw26983step1 raw26983step0; decide +kernel
      have hl : raw26983step0Labels = labelEmbedding6 ∘ raw26983step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26983step0 raw26983step0Labels raw26983step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw26984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26984step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26984 raw26984Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw26984 raw26984Labels = mixedMoment B raw26984step0 raw26984step0Labels := by
      have ha : raw26984step0 = (fun i j => raw26984 (permutation251 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26984step0 raw26984; decide +kernel
      have hl : raw26984step0Labels = raw26984Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26984 raw26984Labels permutation251 permutation3
    mixedMoment B raw26984step0 raw26984step0Labels = mixedMoment B raw26984step1 raw26984step1Labels := by
      have ha : raw26984step1 = raw26984step0 := by apply Matrix.ext; unfold raw26984step1 raw26984step0; decide +kernel
      have hl : raw26984step0Labels = labelEmbedding6 ∘ raw26984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26984step0 raw26984step0Labels raw26984step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw26985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26985step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26985 raw26985Labels = mixedMoment B node4098 node4098Labels := by
  calc
    mixedMoment B raw26985 raw26985Labels = mixedMoment B raw26985step0 raw26985step0Labels := by
      have ha : raw26985step0 = (fun i j => raw26985 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26985step0 raw26985; decide +kernel
      have hl : raw26985step0Labels = raw26985Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26985 raw26985Labels permutation168 permutation3
    mixedMoment B raw26985step0 raw26985step0Labels = mixedMoment B raw26985step1 raw26985step1Labels := by
      have ha : raw26985step1 = raw26985step0 := by apply Matrix.ext; unfold raw26985step1 raw26985step0; decide +kernel
      have hl : raw26985step0Labels = labelEmbedding6 ∘ raw26985step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26985step0 raw26985step0Labels raw26985step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4098 node4098Labels := by rfl

def raw26986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26986step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26986 raw26986Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw26986 raw26986Labels = mixedMoment B raw26986step0 raw26986step0Labels := by
      have ha : raw26986step0 = (fun i j => raw26986 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26986step0 raw26986; decide +kernel
      have hl : raw26986step0Labels = raw26986Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26986 raw26986Labels permutation168 permutation3
    mixedMoment B raw26986step0 raw26986step0Labels = mixedMoment B raw26986step1 raw26986step1Labels := by
      have ha : raw26986step1 = raw26986step0 := by apply Matrix.ext; unfold raw26986step1 raw26986step0; decide +kernel
      have hl : raw26986step0Labels = labelEmbedding6 ∘ raw26986step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26986step0 raw26986step0Labels raw26986step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

def raw26987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26987step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26987 raw26987Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw26987 raw26987Labels = mixedMoment B raw26987step0 raw26987step0Labels := by
      have ha : raw26987step0 = (fun i j => raw26987 (permutation228 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26987step0 raw26987; decide +kernel
      have hl : raw26987step0Labels = raw26987Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26987 raw26987Labels permutation228 permutation3
    mixedMoment B raw26987step0 raw26987step0Labels = mixedMoment B raw26987step1 raw26987step1Labels := by
      have ha : raw26987step1 = raw26987step0 := by apply Matrix.ext; unfold raw26987step1 raw26987step0; decide +kernel
      have hl : raw26987step0Labels = labelEmbedding6 ∘ raw26987step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26987step0 raw26987step0Labels raw26987step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw26988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26988step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26988step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26988 raw26988Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw26988 raw26988Labels = mixedMoment B raw26988step0 raw26988step0Labels := by
      have ha : raw26988step0 = (fun i j => raw26988 (permutation250 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26988step0 raw26988; decide +kernel
      have hl : raw26988step0Labels = raw26988Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26988 raw26988Labels permutation250 permutation3
    mixedMoment B raw26988step0 raw26988step0Labels = mixedMoment B raw26988step1 raw26988step1Labels := by
      have ha : raw26988step1 = raw26988step0 := by apply Matrix.ext; unfold raw26988step1 raw26988step0; decide +kernel
      have hl : raw26988step0Labels = labelEmbedding6 ∘ raw26988step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26988step0 raw26988step0Labels raw26988step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw26989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26989step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26989 raw26989Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw26989 raw26989Labels = mixedMoment B raw26989step0 raw26989step0Labels := by
      have ha : raw26989step0 = (fun i j => raw26989 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26989step0 raw26989; decide +kernel
      have hl : raw26989step0Labels = raw26989Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26989 raw26989Labels permutation170 permutation3
    mixedMoment B raw26989step0 raw26989step0Labels = mixedMoment B raw26989step1 raw26989step1Labels := by
      have ha : raw26989step1 = raw26989step0 := by apply Matrix.ext; unfold raw26989step1 raw26989step0; decide +kernel
      have hl : raw26989step0Labels = labelEmbedding6 ∘ raw26989step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26989step0 raw26989step0Labels raw26989step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4100 node4100Labels := by rfl

def raw26990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26990step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26990 raw26990Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw26990 raw26990Labels = mixedMoment B raw26990step0 raw26990step0Labels := by
      have ha : raw26990step0 = (fun i j => raw26990 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26990step0 raw26990; decide +kernel
      have hl : raw26990step0Labels = raw26990Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26990 raw26990Labels permutation170 permutation3
    mixedMoment B raw26990step0 raw26990step0Labels = mixedMoment B raw26990step1 raw26990step1Labels := by
      have ha : raw26990step1 = raw26990step0 := by apply Matrix.ext; unfold raw26990step1 raw26990step0; decide +kernel
      have hl : raw26990step0Labels = labelEmbedding6 ∘ raw26990step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26990step0 raw26990step0Labels raw26990step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw26991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw26991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26991step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26991step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26991 raw26991Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw26991 raw26991Labels = mixedMoment B raw26991step0 raw26991step0Labels := by
      have ha : raw26991step0 = (fun i j => raw26991 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26991step0 raw26991; decide +kernel
      have hl : raw26991step0Labels = raw26991Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26991 raw26991Labels permutation246 permutation3
    mixedMoment B raw26991step0 raw26991step0Labels = mixedMoment B raw26991step1 raw26991step1Labels := by
      have ha : raw26991step1 = raw26991step0 := by apply Matrix.ext; unfold raw26991step1 raw26991step0; decide +kernel
      have hl : raw26991step0Labels = labelEmbedding6 ∘ raw26991step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26991step0 raw26991step0Labels raw26991step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw26992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26992step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26992 raw26992Labels = mixedMoment B node2593 node2593Labels := by
  calc
    mixedMoment B raw26992 raw26992Labels = mixedMoment B raw26992step0 raw26992step0Labels := by
      have ha : raw26992step0 = (fun i j => raw26992 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26992step0 raw26992; decide +kernel
      have hl : raw26992step0Labels = raw26992Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26992 raw26992Labels permutation168 permutation3
    _ = mixedMoment B node2593 node2593Labels := by rfl

def raw26993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26993step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26993 raw26993Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw26993 raw26993Labels = mixedMoment B raw26993step0 raw26993step0Labels := by
      have hz : ∀ j, raw26993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26993step0 = (fun i j => raw26993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26993step0 raw26993; decide +kernel
      have hl : raw26993step0Labels = raw26993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26993 raw26993Labels permutation434 hz
    mixedMoment B raw26993step0 raw26993step0Labels = mixedMoment B raw26993step1 raw26993step1Labels := by
      have ha : raw26993step1 = (fun i j => raw26993step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26993step1 raw26993step0; decide +kernel
      have hl : raw26993step1Labels = raw26993step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26993step0 raw26993step0Labels permutation35 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw26994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26994 raw26994Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw26994 raw26994Labels = mixedMoment B raw26994step0 raw26994step0Labels := by
      have ha : raw26994step0 = (fun i j => raw26994 (permutation228 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26994step0 raw26994; decide +kernel
      have hl : raw26994step0Labels = raw26994Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26994 raw26994Labels permutation228 permutation3
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw26995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26995 raw26995Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw26995 raw26995Labels = mixedMoment B raw26995step0 raw26995step0Labels := by
      have ha : raw26995step0 = (fun i j => raw26995 (permutation250 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26995step0 raw26995; decide +kernel
      have hl : raw26995step0Labels = raw26995Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26995 raw26995Labels permutation250 permutation3
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw26996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26996 raw26996Labels = mixedMoment B node550 node550Labels := by
  calc
    mixedMoment B raw26996 raw26996Labels = mixedMoment B raw26996step0 raw26996step0Labels := by
      have ha : raw26996step0 = (fun i j => raw26996 (permutation243 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26996step0 raw26996; decide +kernel
      have hl : raw26996step0Labels = raw26996Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26996 raw26996Labels permutation243 permutation3
    _ = mixedMoment B node550 node550Labels := by rfl

def raw26997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26997step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26997 raw26997Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw26997 raw26997Labels = mixedMoment B raw26997step0 raw26997step0Labels := by
      have hz : ∀ j, raw26997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26997step0 = (fun i j => raw26997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26997step0 raw26997; decide +kernel
      have hl : raw26997step0Labels = raw26997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26997 raw26997Labels permutation434 hz
    mixedMoment B raw26997step0 raw26997step0Labels = mixedMoment B raw26997step1 raw26997step1Labels := by
      have ha : raw26997step1 = (fun i j => raw26997step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26997step1 raw26997step0; decide +kernel
      have hl : raw26997step1Labels = raw26997step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26997step0 raw26997step0Labels permutation49 permutation3
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw26998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26998 raw26998Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw26998 raw26998Labels = mixedMoment B raw26998step0 raw26998step0Labels := by
      have ha : raw26998step0 = (fun i j => raw26998 (permutation243 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26998step0 raw26998; decide +kernel
      have hl : raw26998step0Labels = raw26998Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26998 raw26998Labels permutation243 permutation3
    _ = mixedMoment B node998 node998Labels := by rfl

def raw26999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26999 raw26999Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw26999 raw26999Labels = mixedMoment B raw26999step0 raw26999step0Labels := by
      have ha : raw26999step0 = (fun i j => raw26999 (permutation263 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26999step0 raw26999; decide +kernel
      have hl : raw26999step0Labels = raw26999Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26999 raw26999Labels permutation263 permutation3
    _ = mixedMoment B node998 node998Labels := by rfl

def raw27000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27000Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27000 raw27000Labels = mixedMoment B node535 node535Labels := by
  calc
    mixedMoment B raw27000 raw27000Labels = mixedMoment B raw27000step0 raw27000step0Labels := by
      have ha : raw27000step0 = (fun i j => raw27000 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27000step0 raw27000; decide +kernel
      have hl : raw27000step0Labels = raw27000Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27000 raw27000Labels permutation169 permutation3
    _ = mixedMoment B node535 node535Labels := by rfl

def raw27001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27001Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27001 raw27001Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw27001 raw27001Labels = mixedMoment B raw27001step0 raw27001step0Labels := by
      have ha : raw27001step0 = (fun i j => raw27001 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27001step0 raw27001; decide +kernel
      have hl : raw27001step0Labels = raw27001Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27001 raw27001Labels permutation169 permutation3
    _ = mixedMoment B node919 node919Labels := by rfl

def raw27002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27002Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27002step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27002 raw27002Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw27002 raw27002Labels = mixedMoment B raw27002step0 raw27002step0Labels := by
      have hz : ∀ j, raw27002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27002step0 = (fun i j => raw27002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27002step0 raw27002; decide +kernel
      have hl : raw27002step0Labels = raw27002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27002 raw27002Labels permutation434 hz
    mixedMoment B raw27002step0 raw27002step0Labels = mixedMoment B raw27002step1 raw27002step1Labels := by
      have ha : raw27002step1 = (fun i j => raw27002step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27002step1 raw27002step0; decide +kernel
      have hl : raw27002step1Labels = raw27002step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27002step0 raw27002step0Labels permutation35 permutation3
    _ = mixedMoment B node1040 node1040Labels := by rfl

def raw27003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw27003Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27003 raw27003Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw27003 raw27003Labels = mixedMoment B raw27003step0 raw27003step0Labels := by
      have ha : raw27003step0 = (fun i j => raw27003 (permutation229 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27003step0 raw27003; decide +kernel
      have hl : raw27003step0Labels = raw27003Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27003 raw27003Labels permutation229 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

def raw27004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw27004Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27004 raw27004Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw27004 raw27004Labels = mixedMoment B raw27004step0 raw27004step0Labels := by
      have ha : raw27004step0 = (fun i j => raw27004 (permutation251 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27004step0 raw27004; decide +kernel
      have hl : raw27004step0Labels = raw27004Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27004 raw27004Labels permutation251 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

def raw27005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27005Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27005 raw27005Labels = mixedMoment B node535 node535Labels := by
  calc
    mixedMoment B raw27005 raw27005Labels = mixedMoment B raw27005step0 raw27005step0Labels := by
      have ha : raw27005step0 = (fun i j => raw27005 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27005step0 raw27005; decide +kernel
      have hl : raw27005step0Labels = raw27005Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27005 raw27005Labels permutation168 permutation3
    _ = mixedMoment B node535 node535Labels := by rfl

def raw27006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27006Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27006 raw27006Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw27006 raw27006Labels = mixedMoment B raw27006step0 raw27006step0Labels := by
      have ha : raw27006step0 = (fun i j => raw27006 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27006step0 raw27006; decide +kernel
      have hl : raw27006step0Labels = raw27006Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27006 raw27006Labels permutation168 permutation3
    _ = mixedMoment B node919 node919Labels := by rfl

def raw27007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw27007Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27007 raw27007Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw27007 raw27007Labels = mixedMoment B raw27007step0 raw27007step0Labels := by
      have ha : raw27007step0 = (fun i j => raw27007 (permutation228 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27007step0 raw27007; decide +kernel
      have hl : raw27007step0Labels = raw27007Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27007 raw27007Labels permutation228 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
