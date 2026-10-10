import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8832 raw8832Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw8832 raw8832Labels = mixedMoment B raw8832step0 raw8832step0Labels := by
      have ha : raw8832step0 = (fun i j => raw8832 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8832step0 raw8832; decide +kernel
      have hl : raw8832step0Labels = raw8832Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8832 raw8832Labels permutation682 permutation3
    mixedMoment B raw8832step0 raw8832step0Labels = mixedMoment B raw8832step1 raw8832step1Labels := by
      have ha : raw8832step1 = -raw8832step0 := by apply Matrix.ext; change ∀ i j, raw8832step1 i j = -(raw8832step0 i j); unfold raw8832step1 raw8832step0; decide +kernel
      have hl : raw8832step1Labels = raw8832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw8833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8833step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8833 raw8833Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw8833 raw8833Labels = mixedMoment B raw8833step0 raw8833step0Labels := by
      have hz : ∀ j, raw8833 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8833step0 = (fun i j => raw8833 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8833step0 raw8833; decide +kernel
      have hl : raw8833step0Labels = raw8833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8833 raw8833Labels permutation265 hz
    mixedMoment B raw8833step0 raw8833step0Labels = mixedMoment B raw8833step1 raw8833step1Labels := by
      have ha : raw8833step1 = (fun i j => raw8833step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8833step1 raw8833step0; decide +kernel
      have hl : raw8833step1Labels = raw8833step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8833step0 raw8833step0Labels permutation151 permutation3
    mixedMoment B raw8833step1 raw8833step1Labels = mixedMoment B raw8833step2 raw8833step2Labels := by
      have ha : raw8833step2 = -raw8833step1 := by apply Matrix.ext; change ∀ i j, raw8833step2 i j = -(raw8833step1 i j); unfold raw8833step2 raw8833step1; decide +kernel
      have hl : raw8833step2Labels = raw8833step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw8834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8834 raw8834Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw8834 raw8834Labels = mixedMoment B raw8834step0 raw8834step0Labels := by
      have hz : ∀ j, raw8834 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8834step0 = (fun i j => raw8834 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8834step0 raw8834; decide +kernel
      have hl : raw8834step0Labels = raw8834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8834 raw8834Labels permutation265 hz
    mixedMoment B raw8834step0 raw8834step0Labels = mixedMoment B raw8834step1 raw8834step1Labels := by
      have ha : raw8834step1 = (fun i j => raw8834step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8834step1 raw8834step0; decide +kernel
      have hl : raw8834step1Labels = raw8834step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8834step0 raw8834step0Labels permutation149 permutation3
    mixedMoment B raw8834step1 raw8834step1Labels = mixedMoment B raw8834step2 raw8834step2Labels := by
      have ha : raw8834step2 = -raw8834step1 := by apply Matrix.ext; change ∀ i j, raw8834step2 i j = -(raw8834step1 i j); unfold raw8834step2 raw8834step1; decide +kernel
      have hl : raw8834step2Labels = raw8834step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw8835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw8835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw8835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8835 raw8835Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw8835 raw8835Labels = mixedMoment B raw8835step0 raw8835step0Labels := by
      have hz : ∀ j, raw8835 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8835step0 = (fun i j => raw8835 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8835step0 raw8835; decide +kernel
      have hl : raw8835step0Labels = raw8835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8835 raw8835Labels permutation265 hz
    mixedMoment B raw8835step0 raw8835step0Labels = mixedMoment B raw8835step1 raw8835step1Labels := by
      have ha : raw8835step1 = (fun i j => raw8835step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8835step1 raw8835step0; decide +kernel
      have hl : raw8835step1Labels = raw8835step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8835step0 raw8835step0Labels permutation149 permutation3
    mixedMoment B raw8835step1 raw8835step1Labels = mixedMoment B raw8835step2 raw8835step2Labels := by
      have ha : raw8835step2 = -raw8835step1 := by apply Matrix.ext; change ∀ i j, raw8835step2 i j = -(raw8835step1 i j); unfold raw8835step2 raw8835step1; decide +kernel
      have hl : raw8835step2Labels = raw8835step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw8836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8836step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw8836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw8836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8836 raw8836Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw8836 raw8836Labels = mixedMoment B raw8836step0 raw8836step0Labels := by
      have hz : ∀ j, raw8836 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8836step0 = (fun i j => raw8836 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8836step0 raw8836; decide +kernel
      have hl : raw8836step0Labels = raw8836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8836 raw8836Labels permutation265 hz
    mixedMoment B raw8836step0 raw8836step0Labels = mixedMoment B raw8836step1 raw8836step1Labels := by
      have ha : raw8836step1 = (fun i j => raw8836step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8836step1 raw8836step0; decide +kernel
      have hl : raw8836step1Labels = raw8836step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8836step0 raw8836step0Labels permutation48 permutation6
    mixedMoment B raw8836step1 raw8836step1Labels = mixedMoment B raw8836step2 raw8836step2Labels := by
      have ha : raw8836step2 = -raw8836step1 := by apply Matrix.ext; change ∀ i j, raw8836step2 i j = -(raw8836step1 i j); unfold raw8836step2 raw8836step1; decide +kernel
      have hl : raw8836step2Labels = raw8836step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw8837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8837 raw8837Labels = mixedMoment B node1201 node1201Labels := by
  calc
    mixedMoment B raw8837 raw8837Labels = mixedMoment B raw8837step0 raw8837step0Labels := by
      have ha : raw8837step0 = (fun i j => raw8837 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8837step0 raw8837; decide +kernel
      have hl : raw8837step0Labels = raw8837Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8837 raw8837Labels permutation182 permutation3
    _ = mixedMoment B node1201 node1201Labels := by rfl

def raw8838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8838 raw8838Labels = mixedMoment B node2854 node2854Labels := by
  calc
    mixedMoment B raw8838 raw8838Labels = mixedMoment B raw8838step0 raw8838step0Labels := by
      have ha : raw8838step0 = (fun i j => raw8838 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8838step0 raw8838; decide +kernel
      have hl : raw8838step0Labels = raw8838Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8838 raw8838Labels permutation182 permutation3
    _ = mixedMoment B node2854 node2854Labels := by rfl

def raw8839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8839 raw8839Labels = mixedMoment B node2854 node2854Labels := by
  calc
    mixedMoment B raw8839 raw8839Labels = mixedMoment B raw8839step0 raw8839step0Labels := by
      have ha : raw8839step0 = (fun i j => raw8839 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8839step0 raw8839; decide +kernel
      have hl : raw8839step0Labels = raw8839Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8839 raw8839Labels permutation206 permutation3
    _ = mixedMoment B node2854 node2854Labels := by rfl

def raw8840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8840 raw8840Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw8840 raw8840Labels = mixedMoment B raw8840step0 raw8840step0Labels := by
      have ha : raw8840step0 = (fun i j => raw8840 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8840step0 raw8840; decide +kernel
      have hl : raw8840step0Labels = raw8840Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8840 raw8840Labels permutation184 permutation3
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw8841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8841 raw8841Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw8841 raw8841Labels = mixedMoment B raw8841step0 raw8841step0Labels := by
      have ha : raw8841step0 = (fun i j => raw8841 (permutation186 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8841step0 raw8841; decide +kernel
      have hl : raw8841step0Labels = raw8841Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8841 raw8841Labels permutation186 permutation3
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw8842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8842 raw8842Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw8842 raw8842Labels = mixedMoment B raw8842step0 raw8842step0Labels := by
      have hz : ∀ j, raw8842 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8842step0 = (fun i j => raw8842 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8842step0 raw8842; decide +kernel
      have hl : raw8842step0Labels = raw8842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8842 raw8842Labels permutation265 hz
    mixedMoment B raw8842step0 raw8842step0Labels = mixedMoment B raw8842step1 raw8842step1Labels := by
      have ha : raw8842step1 = (fun i j => raw8842step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8842step1 raw8842step0; decide +kernel
      have hl : raw8842step1Labels = raw8842step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8842step0 raw8842step0Labels permutation38 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw8843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8843 raw8843Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw8843 raw8843Labels = mixedMoment B raw8843step0 raw8843step0Labels := by
      have ha : raw8843step0 = (fun i j => raw8843 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8843step0 raw8843; decide +kernel
      have hl : raw8843step0Labels = raw8843Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8843 raw8843Labels permutation158 permutation3
    _ = mixedMoment B node2925 node2925Labels := by rfl

def raw8844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8844 raw8844Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw8844 raw8844Labels = mixedMoment B raw8844step0 raw8844step0Labels := by
      have hz : ∀ j, raw8844 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8844step0 = (fun i j => raw8844 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8844step0 raw8844; decide +kernel
      have hl : raw8844step0Labels = raw8844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8844 raw8844Labels permutation265 hz
    mixedMoment B raw8844step0 raw8844step0Labels = mixedMoment B raw8844step1 raw8844step1Labels := by
      have ha : raw8844step1 = (fun i j => raw8844step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8844step1 raw8844step0; decide +kernel
      have hl : raw8844step1Labels = raw8844step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8844step0 raw8844step0Labels permutation38 permutation3
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw8845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8845 raw8845Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw8845 raw8845Labels = mixedMoment B raw8845step0 raw8845step0Labels := by
      have hz : ∀ j, raw8845 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8845step0 = (fun i j => raw8845 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8845step0 raw8845; decide +kernel
      have hl : raw8845step0Labels = raw8845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8845 raw8845Labels permutation265 hz
    mixedMoment B raw8845step0 raw8845step0Labels = mixedMoment B raw8845step1 raw8845step1Labels := by
      have ha : raw8845step1 = (fun i j => raw8845step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8845step1 raw8845step0; decide +kernel
      have hl : raw8845step1Labels = raw8845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8845step0 raw8845step0Labels permutation40 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw8846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8846step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8846 raw8846Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw8846 raw8846Labels = mixedMoment B raw8846step0 raw8846step0Labels := by
      have hz : ∀ j, raw8846 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8846step0 = (fun i j => raw8846 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8846step0 raw8846; decide +kernel
      have hl : raw8846step0Labels = raw8846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8846 raw8846Labels permutation265 hz
    mixedMoment B raw8846step0 raw8846step0Labels = mixedMoment B raw8846step1 raw8846step1Labels := by
      have ha : raw8846step1 = (fun i j => raw8846step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8846step1 raw8846step0; decide +kernel
      have hl : raw8846step1Labels = raw8846step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8846step0 raw8846step0Labels permutation39 permutation3
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw8847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8847step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8847 raw8847Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw8847 raw8847Labels = mixedMoment B raw8847step0 raw8847step0Labels := by
      have hz : ∀ j, raw8847 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8847step0 = (fun i j => raw8847 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8847step0 raw8847; decide +kernel
      have hl : raw8847step0Labels = raw8847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8847 raw8847Labels permutation265 hz
    mixedMoment B raw8847step0 raw8847step0Labels = mixedMoment B raw8847step1 raw8847step1Labels := by
      have ha : raw8847step1 = (fun i j => raw8847step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8847step1 raw8847step0; decide +kernel
      have hl : raw8847step1Labels = raw8847step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8847step0 raw8847step0Labels permutation32 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw8848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8848 raw8848Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw8848 raw8848Labels = mixedMoment B raw8848step0 raw8848step0Labels := by
      have ha : raw8848step0 = (fun i j => raw8848 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8848step0 raw8848; decide +kernel
      have hl : raw8848step0Labels = raw8848Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8848 raw8848Labels permutation152 permutation3
    _ = mixedMoment B node2925 node2925Labels := by rfl

def raw8849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8849step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8849 raw8849Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw8849 raw8849Labels = mixedMoment B raw8849step0 raw8849step0Labels := by
      have hz : ∀ j, raw8849 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8849step0 = (fun i j => raw8849 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8849step0 raw8849; decide +kernel
      have hl : raw8849step0Labels = raw8849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8849 raw8849Labels permutation265 hz
    mixedMoment B raw8849step0 raw8849step0Labels = mixedMoment B raw8849step1 raw8849step1Labels := by
      have ha : raw8849step1 = (fun i j => raw8849step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8849step1 raw8849step0; decide +kernel
      have hl : raw8849step1Labels = raw8849step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8849step0 raw8849step0Labels permutation32 permutation3
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw8850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8850 raw8850Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw8850 raw8850Labels = mixedMoment B raw8850step0 raw8850step0Labels := by
      have hz : ∀ j, raw8850 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8850step0 = (fun i j => raw8850 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8850step0 raw8850; decide +kernel
      have hl : raw8850step0Labels = raw8850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8850 raw8850Labels permutation265 hz
    mixedMoment B raw8850step0 raw8850step0Labels = mixedMoment B raw8850step1 raw8850step1Labels := by
      have ha : raw8850step1 = (fun i j => raw8850step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8850step1 raw8850step0; decide +kernel
      have hl : raw8850step1Labels = raw8850step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8850step0 raw8850step0Labels permutation34 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw8851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8851 raw8851Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw8851 raw8851Labels = mixedMoment B raw8851step0 raw8851step0Labels := by
      have hz : ∀ j, raw8851 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8851step0 = (fun i j => raw8851 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8851step0 raw8851; decide +kernel
      have hl : raw8851step0Labels = raw8851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8851 raw8851Labels permutation265 hz
    mixedMoment B raw8851step0 raw8851step0Labels = mixedMoment B raw8851step1 raw8851step1Labels := by
      have ha : raw8851step1 = (fun i j => raw8851step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8851step1 raw8851step0; decide +kernel
      have hl : raw8851step1Labels = raw8851step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8851step0 raw8851step0Labels permutation33 permutation3
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw8852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8852step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw8852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8852 raw8852Labels = mixedMoment B node1204 node1204Labels := by
  calc
    mixedMoment B raw8852 raw8852Labels = mixedMoment B raw8852step0 raw8852step0Labels := by
      have hz : ∀ j, raw8852 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8852step0 = (fun i j => raw8852 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8852step0 raw8852; decide +kernel
      have hl : raw8852step0Labels = raw8852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8852 raw8852Labels permutation265 hz
    mixedMoment B raw8852step0 raw8852step0Labels = mixedMoment B raw8852step1 raw8852step1Labels := by
      have ha : raw8852step1 = (fun i j => raw8852step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8852step1 raw8852step0; decide +kernel
      have hl : raw8852step1Labels = raw8852step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8852step0 raw8852step0Labels permutation33 permutation3
    _ = mixedMoment B node1204 node1204Labels := by rfl

def raw8853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw8853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8853 raw8853Labels = mixedMoment B node2912 node2912Labels := by
  calc
    mixedMoment B raw8853 raw8853Labels = mixedMoment B raw8853step0 raw8853step0Labels := by
      have ha : raw8853step0 = (fun i j => raw8853 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8853step0 raw8853; decide +kernel
      have hl : raw8853step0Labels = raw8853Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8853 raw8853Labels permutation153 permutation3
    _ = mixedMoment B node2912 node2912Labels := by rfl

def raw8854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8854step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw8854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8854 raw8854Labels = mixedMoment B node2855 node2855Labels := by
  calc
    mixedMoment B raw8854 raw8854Labels = mixedMoment B raw8854step0 raw8854step0Labels := by
      have hz : ∀ j, raw8854 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8854step0 = (fun i j => raw8854 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8854step0 raw8854; decide +kernel
      have hl : raw8854step0Labels = raw8854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8854 raw8854Labels permutation265 hz
    mixedMoment B raw8854step0 raw8854step0Labels = mixedMoment B raw8854step1 raw8854step1Labels := by
      have ha : raw8854step1 = (fun i j => raw8854step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8854step1 raw8854step0; decide +kernel
      have hl : raw8854step1Labels = raw8854step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8854step0 raw8854step0Labels permutation33 permutation3
    _ = mixedMoment B node2855 node2855Labels := by rfl

def raw8855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8855step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw8855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8855 raw8855Labels = mixedMoment B node2855 node2855Labels := by
  calc
    mixedMoment B raw8855 raw8855Labels = mixedMoment B raw8855step0 raw8855step0Labels := by
      have hz : ∀ j, raw8855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8855step0 = (fun i j => raw8855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8855step0 raw8855; decide +kernel
      have hl : raw8855step0Labels = raw8855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8855 raw8855Labels permutation265 hz
    mixedMoment B raw8855step0 raw8855step0Labels = mixedMoment B raw8855step1 raw8855step1Labels := by
      have ha : raw8855step1 = (fun i j => raw8855step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8855step1 raw8855step0; decide +kernel
      have hl : raw8855step1Labels = raw8855step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8855step0 raw8855step0Labels permutation39 permutation3
    _ = mixedMoment B node2855 node2855Labels := by rfl

def raw8856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw8856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw8856step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8856 raw8856Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw8856 raw8856Labels = mixedMoment B raw8856step0 raw8856step0Labels := by
      have hz : ∀ j, raw8856 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8856step0 = (fun i j => raw8856 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8856step0 raw8856; decide +kernel
      have hl : raw8856step0Labels = raw8856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8856 raw8856Labels permutation265 hz
    mixedMoment B raw8856step0 raw8856step0Labels = mixedMoment B raw8856step1 raw8856step1Labels := by
      have ha : raw8856step1 = (fun i j => raw8856step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8856step1 raw8856step0; decide +kernel
      have hl : raw8856step1Labels = raw8856step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8856step0 raw8856step0Labels permutation33 permutation3
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw8857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8857step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw8857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8857 raw8857Labels = mixedMoment B node1203 node1203Labels := by
  calc
    mixedMoment B raw8857 raw8857Labels = mixedMoment B raw8857step0 raw8857step0Labels := by
      have hz : ∀ j, raw8857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8857step0 = (fun i j => raw8857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8857step0 raw8857; decide +kernel
      have hl : raw8857step0Labels = raw8857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8857 raw8857Labels permutation265 hz
    mixedMoment B raw8857step0 raw8857step0Labels = mixedMoment B raw8857step1 raw8857step1Labels := by
      have ha : raw8857step1 = (fun i j => raw8857step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8857step1 raw8857step0; decide +kernel
      have hl : raw8857step1Labels = raw8857step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8857step0 raw8857step0Labels permutation32 permutation3
    _ = mixedMoment B node1203 node1203Labels := by rfl

def raw8858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw8858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8858 raw8858Labels = mixedMoment B node2378 node2378Labels := by
  calc
    mixedMoment B raw8858 raw8858Labels = mixedMoment B raw8858step0 raw8858step0Labels := by
      have ha : raw8858step0 = (fun i j => raw8858 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8858step0 raw8858; decide +kernel
      have hl : raw8858step0Labels = raw8858Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8858 raw8858Labels permutation682 permutation3
    mixedMoment B raw8858step0 raw8858step0Labels = mixedMoment B raw8858step1 raw8858step1Labels := by
      have ha : raw8858step1 = -raw8858step0 := by apply Matrix.ext; change ∀ i j, raw8858step1 i j = -(raw8858step0 i j); unfold raw8858step1 raw8858step0; decide +kernel
      have hl : raw8858step1Labels = raw8858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2378 node2378Labels := by rfl

def raw8859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8859step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw8859step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw8859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8859 raw8859Labels = mixedMoment B node2386 node2386Labels := by
  calc
    mixedMoment B raw8859 raw8859Labels = mixedMoment B raw8859step0 raw8859step0Labels := by
      have hz : ∀ j, raw8859 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8859step0 = (fun i j => raw8859 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8859step0 raw8859; decide +kernel
      have hl : raw8859step0Labels = raw8859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8859 raw8859Labels permutation265 hz
    mixedMoment B raw8859step0 raw8859step0Labels = mixedMoment B raw8859step1 raw8859step1Labels := by
      have ha : raw8859step1 = (fun i j => raw8859step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8859step1 raw8859step0; decide +kernel
      have hl : raw8859step1Labels = raw8859step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8859step0 raw8859step0Labels permutation151 permutation3
    mixedMoment B raw8859step1 raw8859step1Labels = mixedMoment B raw8859step2 raw8859step2Labels := by
      have ha : raw8859step2 = -raw8859step1 := by apply Matrix.ext; change ∀ i j, raw8859step2 i j = -(raw8859step1 i j); unfold raw8859step2 raw8859step1; decide +kernel
      have hl : raw8859step2Labels = raw8859step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2386 node2386Labels := by rfl

def raw8860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8860step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw8860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw8860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8860 raw8860Labels = mixedMoment B node2386 node2386Labels := by
  calc
    mixedMoment B raw8860 raw8860Labels = mixedMoment B raw8860step0 raw8860step0Labels := by
      have hz : ∀ j, raw8860 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8860step0 = (fun i j => raw8860 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8860step0 raw8860; decide +kernel
      have hl : raw8860step0Labels = raw8860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8860 raw8860Labels permutation265 hz
    mixedMoment B raw8860step0 raw8860step0Labels = mixedMoment B raw8860step1 raw8860step1Labels := by
      have ha : raw8860step1 = (fun i j => raw8860step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8860step1 raw8860step0; decide +kernel
      have hl : raw8860step1Labels = raw8860step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8860step0 raw8860step0Labels permutation149 permutation3
    mixedMoment B raw8860step1 raw8860step1Labels = mixedMoment B raw8860step2 raw8860step2Labels := by
      have ha : raw8860step2 = -raw8860step1 := by apply Matrix.ext; change ∀ i j, raw8860step2 i j = -(raw8860step1 i j); unfold raw8860step2 raw8860step1; decide +kernel
      have hl : raw8860step2Labels = raw8860step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2386 node2386Labels := by rfl

def raw8861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw8861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw8861step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw8861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw8861step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8861 raw8861Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw8861 raw8861Labels = mixedMoment B raw8861step0 raw8861step0Labels := by
      have hz : ∀ j, raw8861 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8861step0 = (fun i j => raw8861 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8861step0 raw8861; decide +kernel
      have hl : raw8861step0Labels = raw8861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8861 raw8861Labels permutation265 hz
    mixedMoment B raw8861step0 raw8861step0Labels = mixedMoment B raw8861step1 raw8861step1Labels := by
      have ha : raw8861step1 = (fun i j => raw8861step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8861step1 raw8861step0; decide +kernel
      have hl : raw8861step1Labels = raw8861step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8861step0 raw8861step0Labels permutation149 permutation3
    mixedMoment B raw8861step1 raw8861step1Labels = mixedMoment B raw8861step2 raw8861step2Labels := by
      have ha : raw8861step2 = -raw8861step1 := by apply Matrix.ext; change ∀ i j, raw8861step2 i j = -(raw8861step1 i j); unfold raw8861step2 raw8861step1; decide +kernel
      have hl : raw8861step2Labels = raw8861step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw8862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8862step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8862step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8862 raw8862Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw8862 raw8862Labels = mixedMoment B raw8862step0 raw8862step0Labels := by
      have ha : raw8862step0 = (fun i j => raw8862 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8862step0 raw8862; decide +kernel
      have hl : raw8862step0Labels = raw8862Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8862 raw8862Labels permutation224 permutation7
    mixedMoment B raw8862step0 raw8862step0Labels = mixedMoment B raw8862step1 raw8862step1Labels := by
      have ha : raw8862step1 = -raw8862step0 := by apply Matrix.ext; change ∀ i j, raw8862step1 i j = -(raw8862step0 i j); unfold raw8862step1 raw8862step0; decide +kernel
      have hl : raw8862step1Labels = raw8862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8862step1 raw8862step1Labels = mixedMoment B raw8862step2 raw8862step2Labels := by
      have ha : raw8862step2 = raw8862step1 := by apply Matrix.ext; unfold raw8862step2 raw8862step1; decide +kernel
      have hl : raw8862step1Labels = labelEmbedding1 ∘ raw8862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8862step1 raw8862step1Labels raw8862step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw8863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8863step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw8863step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8863step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8863step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8863step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8863 raw8863Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw8863 raw8863Labels = mixedMoment B raw8863step0 raw8863step0Labels := by
      have hz : ∀ j, raw8863 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8863step0 = (fun i j => raw8863 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8863step0 raw8863; decide +kernel
      have hl : raw8863step0Labels = raw8863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8863 raw8863Labels permutation265 hz
    mixedMoment B raw8863step0 raw8863step0Labels = mixedMoment B raw8863step1 raw8863step1Labels := by
      have ha : raw8863step1 = (fun i j => raw8863step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8863step1 raw8863step0; decide +kernel
      have hl : raw8863step1Labels = raw8863step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8863step0 raw8863step0Labels permutation44 permutation7
    mixedMoment B raw8863step1 raw8863step1Labels = mixedMoment B raw8863step2 raw8863step2Labels := by
      have ha : raw8863step2 = -raw8863step1 := by apply Matrix.ext; change ∀ i j, raw8863step2 i j = -(raw8863step1 i j); unfold raw8863step2 raw8863step1; decide +kernel
      have hl : raw8863step2Labels = raw8863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8863step2 raw8863step2Labels = mixedMoment B raw8863step3 raw8863step3Labels := by
      have ha : raw8863step3 = raw8863step2 := by apply Matrix.ext; unfold raw8863step3 raw8863step2; decide +kernel
      have hl : raw8863step2Labels = labelEmbedding1 ∘ raw8863step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8863step2 raw8863step2Labels raw8863step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw8864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8864step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw8864step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8864step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8864step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8864step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8864 raw8864Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw8864 raw8864Labels = mixedMoment B raw8864step0 raw8864step0Labels := by
      have hz : ∀ j, raw8864 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8864step0 = (fun i j => raw8864 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8864step0 raw8864; decide +kernel
      have hl : raw8864step0Labels = raw8864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8864 raw8864Labels permutation265 hz
    mixedMoment B raw8864step0 raw8864step0Labels = mixedMoment B raw8864step1 raw8864step1Labels := by
      have ha : raw8864step1 = (fun i j => raw8864step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8864step1 raw8864step0; decide +kernel
      have hl : raw8864step1Labels = raw8864step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8864step0 raw8864step0Labels permutation46 permutation7
    mixedMoment B raw8864step1 raw8864step1Labels = mixedMoment B raw8864step2 raw8864step2Labels := by
      have ha : raw8864step2 = -raw8864step1 := by apply Matrix.ext; change ∀ i j, raw8864step2 i j = -(raw8864step1 i j); unfold raw8864step2 raw8864step1; decide +kernel
      have hl : raw8864step2Labels = raw8864step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8864step2 raw8864step2Labels = mixedMoment B raw8864step3 raw8864step3Labels := by
      have ha : raw8864step3 = raw8864step2 := by apply Matrix.ext; unfold raw8864step3 raw8864step2; decide +kernel
      have hl : raw8864step2Labels = labelEmbedding1 ∘ raw8864step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8864step2 raw8864step2Labels raw8864step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw8865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8865step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8865step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8865step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8865step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8865 raw8865Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw8865 raw8865Labels = mixedMoment B raw8865step0 raw8865step0Labels := by
      have hz : ∀ j, raw8865 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8865step0 = (fun i j => raw8865 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8865step0 raw8865; decide +kernel
      have hl : raw8865step0Labels = raw8865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8865 raw8865Labels permutation265 hz
    mixedMoment B raw8865step0 raw8865step0Labels = mixedMoment B raw8865step1 raw8865step1Labels := by
      have ha : raw8865step1 = (fun i j => raw8865step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8865step1 raw8865step0; decide +kernel
      have hl : raw8865step1Labels = raw8865step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8865step0 raw8865step0Labels permutation44 permutation7
    mixedMoment B raw8865step1 raw8865step1Labels = mixedMoment B raw8865step2 raw8865step2Labels := by
      have ha : raw8865step2 = -raw8865step1 := by apply Matrix.ext; change ∀ i j, raw8865step2 i j = -(raw8865step1 i j); unfold raw8865step2 raw8865step1; decide +kernel
      have hl : raw8865step2Labels = raw8865step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8865step2 raw8865step2Labels = mixedMoment B raw8865step3 raw8865step3Labels := by
      have ha : raw8865step3 = raw8865step2 := by apply Matrix.ext; unfold raw8865step3 raw8865step2; decide +kernel
      have hl : raw8865step2Labels = labelEmbedding1 ∘ raw8865step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8865step2 raw8865step2Labels raw8865step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw8866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8866step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw8866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8866step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8866step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8866step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8866 raw8866Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw8866 raw8866Labels = mixedMoment B raw8866step0 raw8866step0Labels := by
      have hz : ∀ j, raw8866 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8866step0 = (fun i j => raw8866 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8866step0 raw8866; decide +kernel
      have hl : raw8866step0Labels = raw8866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8866 raw8866Labels permutation265 hz
    mixedMoment B raw8866step0 raw8866step0Labels = mixedMoment B raw8866step1 raw8866step1Labels := by
      have ha : raw8866step1 = (fun i j => raw8866step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8866step1 raw8866step0; decide +kernel
      have hl : raw8866step1Labels = raw8866step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8866step0 raw8866step0Labels permutation44 permutation7
    mixedMoment B raw8866step1 raw8866step1Labels = mixedMoment B raw8866step2 raw8866step2Labels := by
      have ha : raw8866step2 = -raw8866step1 := by apply Matrix.ext; change ∀ i j, raw8866step2 i j = -(raw8866step1 i j); unfold raw8866step2 raw8866step1; decide +kernel
      have hl : raw8866step2Labels = raw8866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8866step2 raw8866step2Labels = mixedMoment B raw8866step3 raw8866step3Labels := by
      have ha : raw8866step3 = raw8866step2 := by apply Matrix.ext; unfold raw8866step3 raw8866step2; decide +kernel
      have hl : raw8866step2Labels = labelEmbedding1 ∘ raw8866step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8866step2 raw8866step2Labels raw8866step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw8867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8867Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8867step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8867step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8867step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8867step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8867 raw8867Labels = mixedMoment B node3282 node3282Labels := by
  calc
    mixedMoment B raw8867 raw8867Labels = mixedMoment B raw8867step0 raw8867step0Labels := by
      have ha : raw8867step0 = (fun i j => raw8867 (permutation183 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8867step0 raw8867; decide +kernel
      have hl : raw8867step0Labels = raw8867Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8867 raw8867Labels permutation183 permutation5
    mixedMoment B raw8867step0 raw8867step0Labels = mixedMoment B raw8867step1 raw8867step1Labels := by
      have ha : raw8867step1 = -raw8867step0 := by apply Matrix.ext; change ∀ i j, raw8867step1 i j = -(raw8867step0 i j); unfold raw8867step1 raw8867step0; decide +kernel
      have hl : raw8867step1Labels = raw8867step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8867step1 raw8867step1Labels = mixedMoment B raw8867step2 raw8867step2Labels := by
      have ha : raw8867step2 = raw8867step1 := by apply Matrix.ext; unfold raw8867step2 raw8867step1; decide +kernel
      have hl : raw8867step1Labels = labelEmbedding1 ∘ raw8867step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8867step1 raw8867step1Labels raw8867step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3282 node3282Labels := by rfl

def raw8868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8868Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw8868step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8868step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8868step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8868 raw8868Labels = mixedMoment B node3568 node3568Labels := by
  calc
    mixedMoment B raw8868 raw8868Labels = mixedMoment B raw8868step0 raw8868step0Labels := by
      have ha : raw8868step0 = (fun i j => raw8868 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8868step0 raw8868; decide +kernel
      have hl : raw8868step0Labels = raw8868Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8868 raw8868Labels permutation224 permutation7
    mixedMoment B raw8868step0 raw8868step0Labels = mixedMoment B raw8868step1 raw8868step1Labels := by
      have ha : raw8868step1 = -raw8868step0 := by apply Matrix.ext; change ∀ i j, raw8868step1 i j = -(raw8868step0 i j); unfold raw8868step1 raw8868step0; decide +kernel
      have hl : raw8868step1Labels = raw8868step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8868step1 raw8868step1Labels = mixedMoment B raw8868step2 raw8868step2Labels := by
      have ha : raw8868step2 = raw8868step1 := by apply Matrix.ext; unfold raw8868step2 raw8868step1; decide +kernel
      have hl : raw8868step1Labels = labelEmbedding1 ∘ raw8868step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8868step1 raw8868step1Labels raw8868step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3568 node3568Labels := by rfl

def raw8869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8869Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw8869step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8869step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8869step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8869 raw8869Labels = mixedMoment B node3568 node3568Labels := by
  calc
    mixedMoment B raw8869 raw8869Labels = mixedMoment B raw8869step0 raw8869step0Labels := by
      have ha : raw8869step0 = (fun i j => raw8869 (permutation226 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8869step0 raw8869; decide +kernel
      have hl : raw8869step0Labels = raw8869Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8869 raw8869Labels permutation226 permutation7
    mixedMoment B raw8869step0 raw8869step0Labels = mixedMoment B raw8869step1 raw8869step1Labels := by
      have ha : raw8869step1 = -raw8869step0 := by apply Matrix.ext; change ∀ i j, raw8869step1 i j = -(raw8869step0 i j); unfold raw8869step1 raw8869step0; decide +kernel
      have hl : raw8869step1Labels = raw8869step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8869step1 raw8869step1Labels = mixedMoment B raw8869step2 raw8869step2Labels := by
      have ha : raw8869step2 = raw8869step1 := by apply Matrix.ext; unfold raw8869step2 raw8869step1; decide +kernel
      have hl : raw8869step1Labels = labelEmbedding1 ∘ raw8869step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8869step1 raw8869step1Labels raw8869step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3568 node3568Labels := by rfl

def raw8870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8870Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8870step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8870step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8870step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8870 raw8870Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw8870 raw8870Labels = mixedMoment B raw8870step0 raw8870step0Labels := by
      have ha : raw8870step0 = (fun i j => raw8870 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8870step0 raw8870; decide +kernel
      have hl : raw8870step0Labels = raw8870Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8870 raw8870Labels permutation224 permutation7
    mixedMoment B raw8870step0 raw8870step0Labels = mixedMoment B raw8870step1 raw8870step1Labels := by
      have ha : raw8870step1 = -raw8870step0 := by apply Matrix.ext; change ∀ i j, raw8870step1 i j = -(raw8870step0 i j); unfold raw8870step1 raw8870step0; decide +kernel
      have hl : raw8870step1Labels = raw8870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8870step1 raw8870step1Labels = mixedMoment B raw8870step2 raw8870step2Labels := by
      have ha : raw8870step2 = raw8870step1 := by apply Matrix.ext; unfold raw8870step2 raw8870step1; decide +kernel
      have hl : raw8870step1Labels = labelEmbedding1 ∘ raw8870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8870step1 raw8870step1Labels raw8870step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

def raw8871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8871Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw8871step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8871step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8871step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8871 raw8871Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw8871 raw8871Labels = mixedMoment B raw8871step0 raw8871step0Labels := by
      have ha : raw8871step0 = (fun i j => raw8871 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8871step0 raw8871; decide +kernel
      have hl : raw8871step0Labels = raw8871Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8871 raw8871Labels permutation224 permutation7
    mixedMoment B raw8871step0 raw8871step0Labels = mixedMoment B raw8871step1 raw8871step1Labels := by
      have ha : raw8871step1 = -raw8871step0 := by apply Matrix.ext; change ∀ i j, raw8871step1 i j = -(raw8871step0 i j); unfold raw8871step1 raw8871step0; decide +kernel
      have hl : raw8871step1Labels = raw8871step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8871step1 raw8871step1Labels = mixedMoment B raw8871step2 raw8871step2Labels := by
      have ha : raw8871step2 = raw8871step1 := by apply Matrix.ext; unfold raw8871step2 raw8871step1; decide +kernel
      have hl : raw8871step1Labels = labelEmbedding1 ∘ raw8871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8871step1 raw8871step1Labels raw8871step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw8872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8872Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8872step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8872step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8872step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8872step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8872step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8872 raw8872Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw8872 raw8872Labels = mixedMoment B raw8872step0 raw8872step0Labels := by
      have hz : ∀ j, raw8872 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8872step0 = (fun i j => raw8872 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8872step0 raw8872; decide +kernel
      have hl : raw8872step0Labels = raw8872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8872 raw8872Labels permutation265 hz
    mixedMoment B raw8872step0 raw8872step0Labels = mixedMoment B raw8872step1 raw8872step1Labels := by
      have ha : raw8872step1 = (fun i j => raw8872step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8872step1 raw8872step0; decide +kernel
      have hl : raw8872step1Labels = raw8872step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8872step0 raw8872step0Labels permutation39 permutation5
    mixedMoment B raw8872step1 raw8872step1Labels = mixedMoment B raw8872step2 raw8872step2Labels := by
      have ha : raw8872step2 = -raw8872step1 := by apply Matrix.ext; change ∀ i j, raw8872step2 i j = -(raw8872step1 i j); unfold raw8872step2 raw8872step1; decide +kernel
      have hl : raw8872step2Labels = raw8872step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8872step2 raw8872step2Labels = mixedMoment B raw8872step3 raw8872step3Labels := by
      have ha : raw8872step3 = raw8872step2 := by apply Matrix.ext; unfold raw8872step3 raw8872step2; decide +kernel
      have hl : raw8872step2Labels = labelEmbedding1 ∘ raw8872step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8872step2 raw8872step2Labels raw8872step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw8873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8873step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8873step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8873step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8873 raw8873Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw8873 raw8873Labels = mixedMoment B raw8873step0 raw8873step0Labels := by
      have ha : raw8873step0 = (fun i j => raw8873 (permutation226 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8873step0 raw8873; decide +kernel
      have hl : raw8873step0Labels = raw8873Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8873 raw8873Labels permutation226 permutation7
    mixedMoment B raw8873step0 raw8873step0Labels = mixedMoment B raw8873step1 raw8873step1Labels := by
      have ha : raw8873step1 = -raw8873step0 := by apply Matrix.ext; change ∀ i j, raw8873step1 i j = -(raw8873step0 i j); unfold raw8873step1 raw8873step0; decide +kernel
      have hl : raw8873step1Labels = raw8873step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8873step1 raw8873step1Labels = mixedMoment B raw8873step2 raw8873step2Labels := by
      have ha : raw8873step2 = raw8873step1 := by apply Matrix.ext; unfold raw8873step2 raw8873step1; decide +kernel
      have hl : raw8873step1Labels = labelEmbedding1 ∘ raw8873step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8873step1 raw8873step1Labels raw8873step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw8874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8874step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw8874step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8874step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8874step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8874step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8874 raw8874Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw8874 raw8874Labels = mixedMoment B raw8874step0 raw8874step0Labels := by
      have hz : ∀ j, raw8874 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8874step0 = (fun i j => raw8874 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8874step0 raw8874; decide +kernel
      have hl : raw8874step0Labels = raw8874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8874 raw8874Labels permutation265 hz
    mixedMoment B raw8874step0 raw8874step0Labels = mixedMoment B raw8874step1 raw8874step1Labels := by
      have ha : raw8874step1 = (fun i j => raw8874step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8874step1 raw8874step0; decide +kernel
      have hl : raw8874step1Labels = raw8874step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8874step0 raw8874step0Labels permutation46 permutation7
    mixedMoment B raw8874step1 raw8874step1Labels = mixedMoment B raw8874step2 raw8874step2Labels := by
      have ha : raw8874step2 = -raw8874step1 := by apply Matrix.ext; change ∀ i j, raw8874step2 i j = -(raw8874step1 i j); unfold raw8874step2 raw8874step1; decide +kernel
      have hl : raw8874step2Labels = raw8874step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8874step2 raw8874step2Labels = mixedMoment B raw8874step3 raw8874step3Labels := by
      have ha : raw8874step3 = raw8874step2 := by apply Matrix.ext; unfold raw8874step3 raw8874step2; decide +kernel
      have hl : raw8874step2Labels = labelEmbedding1 ∘ raw8874step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8874step2 raw8874step2Labels raw8874step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw8875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8875Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8875step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8875step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8875step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8875step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8875step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8875 raw8875Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw8875 raw8875Labels = mixedMoment B raw8875step0 raw8875step0Labels := by
      have hz : ∀ j, raw8875 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8875step0 = (fun i j => raw8875 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8875step0 raw8875; decide +kernel
      have hl : raw8875step0Labels = raw8875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8875 raw8875Labels permutation265 hz
    mixedMoment B raw8875step0 raw8875step0Labels = mixedMoment B raw8875step1 raw8875step1Labels := by
      have ha : raw8875step1 = (fun i j => raw8875step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8875step1 raw8875step0; decide +kernel
      have hl : raw8875step1Labels = raw8875step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8875step0 raw8875step0Labels permutation46 permutation7
    mixedMoment B raw8875step1 raw8875step1Labels = mixedMoment B raw8875step2 raw8875step2Labels := by
      have ha : raw8875step2 = -raw8875step1 := by apply Matrix.ext; change ∀ i j, raw8875step2 i j = -(raw8875step1 i j); unfold raw8875step2 raw8875step1; decide +kernel
      have hl : raw8875step2Labels = raw8875step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8875step2 raw8875step2Labels = mixedMoment B raw8875step3 raw8875step3Labels := by
      have ha : raw8875step3 = raw8875step2 := by apply Matrix.ext; unfold raw8875step3 raw8875step2; decide +kernel
      have hl : raw8875step2Labels = labelEmbedding1 ∘ raw8875step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8875step2 raw8875step2Labels raw8875step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw8876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8876Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8876step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw8876step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw8876step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8876step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw8876step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8876 raw8876Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw8876 raw8876Labels = mixedMoment B raw8876step0 raw8876step0Labels := by
      have hz : ∀ j, raw8876 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8876step0 = (fun i j => raw8876 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8876step0 raw8876; decide +kernel
      have hl : raw8876step0Labels = raw8876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8876 raw8876Labels permutation265 hz
    mixedMoment B raw8876step0 raw8876step0Labels = mixedMoment B raw8876step1 raw8876step1Labels := by
      have ha : raw8876step1 = (fun i j => raw8876step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8876step1 raw8876step0; decide +kernel
      have hl : raw8876step1Labels = raw8876step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8876step0 raw8876step0Labels permutation46 permutation7
    mixedMoment B raw8876step1 raw8876step1Labels = mixedMoment B raw8876step2 raw8876step2Labels := by
      have ha : raw8876step2 = -raw8876step1 := by apply Matrix.ext; change ∀ i j, raw8876step2 i j = -(raw8876step1 i j); unfold raw8876step2 raw8876step1; decide +kernel
      have hl : raw8876step2Labels = raw8876step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8876step2 raw8876step2Labels = mixedMoment B raw8876step3 raw8876step3Labels := by
      have ha : raw8876step3 = raw8876step2 := by apply Matrix.ext; unfold raw8876step3 raw8876step2; decide +kernel
      have hl : raw8876step2Labels = labelEmbedding1 ∘ raw8876step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8876step2 raw8876step2Labels raw8876step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw8877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8877Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8877step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8877step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8877step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8877step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8877 raw8877Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw8877 raw8877Labels = mixedMoment B raw8877step0 raw8877step0Labels := by
      have hz : ∀ j, raw8877 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8877step0 = (fun i j => raw8877 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8877step0 raw8877; decide +kernel
      have hl : raw8877step0Labels = raw8877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8877 raw8877Labels permutation265 hz
    mixedMoment B raw8877step0 raw8877step0Labels = mixedMoment B raw8877step1 raw8877step1Labels := by
      have ha : raw8877step1 = (fun i j => raw8877step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8877step1 raw8877step0; decide +kernel
      have hl : raw8877step1Labels = raw8877step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8877step0 raw8877step0Labels permutation33 permutation5
    mixedMoment B raw8877step1 raw8877step1Labels = mixedMoment B raw8877step2 raw8877step2Labels := by
      have ha : raw8877step2 = -raw8877step1 := by apply Matrix.ext; change ∀ i j, raw8877step2 i j = -(raw8877step1 i j); unfold raw8877step2 raw8877step1; decide +kernel
      have hl : raw8877step2Labels = raw8877step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8877step2 raw8877step2Labels = mixedMoment B raw8877step3 raw8877step3Labels := by
      have ha : raw8877step3 = raw8877step2 := by apply Matrix.ext; unfold raw8877step3 raw8877step2; decide +kernel
      have hl : raw8877step2Labels = labelEmbedding1 ∘ raw8877step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8877step2 raw8877step2Labels raw8877step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw8878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8878Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8878step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8878step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8878step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8878step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8878 raw8878Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw8878 raw8878Labels = mixedMoment B raw8878step0 raw8878step0Labels := by
      have ha : raw8878step0 = (fun i j => raw8878 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8878step0 raw8878; decide +kernel
      have hl : raw8878step0Labels = raw8878Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8878 raw8878Labels permutation224 permutation7
    mixedMoment B raw8878step0 raw8878step0Labels = mixedMoment B raw8878step1 raw8878step1Labels := by
      have ha : raw8878step1 = -raw8878step0 := by apply Matrix.ext; change ∀ i j, raw8878step1 i j = -(raw8878step0 i j); unfold raw8878step1 raw8878step0; decide +kernel
      have hl : raw8878step1Labels = raw8878step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8878step1 raw8878step1Labels = mixedMoment B raw8878step2 raw8878step2Labels := by
      have ha : raw8878step2 = raw8878step1 := by apply Matrix.ext; unfold raw8878step2 raw8878step1; decide +kernel
      have hl : raw8878step1Labels = labelEmbedding1 ∘ raw8878step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8878step1 raw8878step1Labels raw8878step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw8879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8879Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8879step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw8879step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8879step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8879step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8879step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8879 raw8879Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw8879 raw8879Labels = mixedMoment B raw8879step0 raw8879step0Labels := by
      have hz : ∀ j, raw8879 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8879step0 = (fun i j => raw8879 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8879step0 raw8879; decide +kernel
      have hl : raw8879step0Labels = raw8879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8879 raw8879Labels permutation265 hz
    mixedMoment B raw8879step0 raw8879step0Labels = mixedMoment B raw8879step1 raw8879step1Labels := by
      have ha : raw8879step1 = (fun i j => raw8879step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8879step1 raw8879step0; decide +kernel
      have hl : raw8879step1Labels = raw8879step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8879step0 raw8879step0Labels permutation44 permutation7
    mixedMoment B raw8879step1 raw8879step1Labels = mixedMoment B raw8879step2 raw8879step2Labels := by
      have ha : raw8879step2 = -raw8879step1 := by apply Matrix.ext; change ∀ i j, raw8879step2 i j = -(raw8879step1 i j); unfold raw8879step2 raw8879step1; decide +kernel
      have hl : raw8879step2Labels = raw8879step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8879step2 raw8879step2Labels = mixedMoment B raw8879step3 raw8879step3Labels := by
      have ha : raw8879step3 = raw8879step2 := by apply Matrix.ext; unfold raw8879step3 raw8879step2; decide +kernel
      have hl : raw8879step2Labels = labelEmbedding1 ∘ raw8879step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8879step2 raw8879step2Labels raw8879step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw8880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8880Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8880step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8880step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8880step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8880step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8880step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8880 raw8880Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw8880 raw8880Labels = mixedMoment B raw8880step0 raw8880step0Labels := by
      have hz : ∀ j, raw8880 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8880step0 = (fun i j => raw8880 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8880step0 raw8880; decide +kernel
      have hl : raw8880step0Labels = raw8880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8880 raw8880Labels permutation265 hz
    mixedMoment B raw8880step0 raw8880step0Labels = mixedMoment B raw8880step1 raw8880step1Labels := by
      have ha : raw8880step1 = (fun i j => raw8880step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8880step1 raw8880step0; decide +kernel
      have hl : raw8880step1Labels = raw8880step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8880step0 raw8880step0Labels permutation44 permutation7
    mixedMoment B raw8880step1 raw8880step1Labels = mixedMoment B raw8880step2 raw8880step2Labels := by
      have ha : raw8880step2 = -raw8880step1 := by apply Matrix.ext; change ∀ i j, raw8880step2 i j = -(raw8880step1 i j); unfold raw8880step2 raw8880step1; decide +kernel
      have hl : raw8880step2Labels = raw8880step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8880step2 raw8880step2Labels = mixedMoment B raw8880step3 raw8880step3Labels := by
      have ha : raw8880step3 = raw8880step2 := by apply Matrix.ext; unfold raw8880step3 raw8880step2; decide +kernel
      have hl : raw8880step2Labels = labelEmbedding1 ∘ raw8880step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8880step2 raw8880step2Labels raw8880step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw8881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8881Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8881step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw8881step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw8881step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8881step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw8881step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8881 raw8881Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw8881 raw8881Labels = mixedMoment B raw8881step0 raw8881step0Labels := by
      have hz : ∀ j, raw8881 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8881step0 = (fun i j => raw8881 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8881step0 raw8881; decide +kernel
      have hl : raw8881step0Labels = raw8881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8881 raw8881Labels permutation265 hz
    mixedMoment B raw8881step0 raw8881step0Labels = mixedMoment B raw8881step1 raw8881step1Labels := by
      have ha : raw8881step1 = (fun i j => raw8881step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8881step1 raw8881step0; decide +kernel
      have hl : raw8881step1Labels = raw8881step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8881step0 raw8881step0Labels permutation44 permutation7
    mixedMoment B raw8881step1 raw8881step1Labels = mixedMoment B raw8881step2 raw8881step2Labels := by
      have ha : raw8881step2 = -raw8881step1 := by apply Matrix.ext; change ∀ i j, raw8881step2 i j = -(raw8881step1 i j); unfold raw8881step2 raw8881step1; decide +kernel
      have hl : raw8881step2Labels = raw8881step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8881step2 raw8881step2Labels = mixedMoment B raw8881step3 raw8881step3Labels := by
      have ha : raw8881step3 = raw8881step2 := by apply Matrix.ext; unfold raw8881step3 raw8881step2; decide +kernel
      have hl : raw8881step2Labels = labelEmbedding1 ∘ raw8881step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8881step2 raw8881step2Labels raw8881step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw8882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8882Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8882step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw8882step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw8882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8882 raw8882Labels = mixedMoment B node2397 node2397Labels := by
  calc
    mixedMoment B raw8882 raw8882Labels = mixedMoment B raw8882step0 raw8882step0Labels := by
      have hz : ∀ j, raw8882 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8882step0 = (fun i j => raw8882 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8882step0 raw8882; decide +kernel
      have hl : raw8882step0Labels = raw8882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8882 raw8882Labels permutation265 hz
    mixedMoment B raw8882step0 raw8882step0Labels = mixedMoment B raw8882step1 raw8882step1Labels := by
      have ha : raw8882step1 = (fun i j => raw8882step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8882step1 raw8882step0; decide +kernel
      have hl : raw8882step1Labels = raw8882step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8882step0 raw8882step0Labels permutation125 permutation5
    mixedMoment B raw8882step1 raw8882step1Labels = mixedMoment B raw8882step2 raw8882step2Labels := by
      have ha : raw8882step2 = raw8882step1 := by apply Matrix.ext; unfold raw8882step2 raw8882step1; decide +kernel
      have hl : raw8882step1Labels = labelEmbedding1 ∘ raw8882step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8882step1 raw8882step1Labels raw8882step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2397 node2397Labels := by rfl

def raw8883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8883Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8883step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8883step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8883 raw8883Labels = mixedMoment B node2396 node2396Labels := by
  calc
    mixedMoment B raw8883 raw8883Labels = mixedMoment B raw8883step0 raw8883step0Labels := by
      have ha : raw8883step0 = (fun i j => raw8883 (permutation584 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8883step0 raw8883; decide +kernel
      have hl : raw8883step0Labels = raw8883Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8883 raw8883Labels permutation584 permutation5
    mixedMoment B raw8883step0 raw8883step0Labels = mixedMoment B raw8883step1 raw8883step1Labels := by
      have ha : raw8883step1 = raw8883step0 := by apply Matrix.ext; unfold raw8883step1 raw8883step0; decide +kernel
      have hl : raw8883step0Labels = labelEmbedding1 ∘ raw8883step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8883step0 raw8883step0Labels raw8883step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2396 node2396Labels := by rfl

def raw8884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8884Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8884step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8884step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8884 raw8884Labels = mixedMoment B node2401 node2401Labels := by
  calc
    mixedMoment B raw8884 raw8884Labels = mixedMoment B raw8884step0 raw8884step0Labels := by
      have hz : ∀ j, raw8884 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8884step0 = (fun i j => raw8884 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8884step0 raw8884; decide +kernel
      have hl : raw8884step0Labels = raw8884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8884 raw8884Labels permutation265 hz
    mixedMoment B raw8884step0 raw8884step0Labels = mixedMoment B raw8884step1 raw8884step1Labels := by
      have ha : raw8884step1 = (fun i j => raw8884step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8884step1 raw8884step0; decide +kernel
      have hl : raw8884step1Labels = raw8884step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8884step0 raw8884step0Labels permutation126 permutation5
    mixedMoment B raw8884step1 raw8884step1Labels = mixedMoment B raw8884step2 raw8884step2Labels := by
      have ha : raw8884step2 = raw8884step1 := by apply Matrix.ext; unfold raw8884step2 raw8884step1; decide +kernel
      have hl : raw8884step1Labels = labelEmbedding1 ∘ raw8884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8884step1 raw8884step1Labels raw8884step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2401 node2401Labels := by rfl

def raw8885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8885Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8885step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8885step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8885step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8885 raw8885Labels = mixedMoment B node2401 node2401Labels := by
  calc
    mixedMoment B raw8885 raw8885Labels = mixedMoment B raw8885step0 raw8885step0Labels := by
      have hz : ∀ j, raw8885 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8885step0 = (fun i j => raw8885 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8885step0 raw8885; decide +kernel
      have hl : raw8885step0Labels = raw8885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8885 raw8885Labels permutation265 hz
    mixedMoment B raw8885step0 raw8885step0Labels = mixedMoment B raw8885step1 raw8885step1Labels := by
      have ha : raw8885step1 = (fun i j => raw8885step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8885step1 raw8885step0; decide +kernel
      have hl : raw8885step1Labels = raw8885step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8885step0 raw8885step0Labels permutation124 permutation5
    mixedMoment B raw8885step1 raw8885step1Labels = mixedMoment B raw8885step2 raw8885step2Labels := by
      have ha : raw8885step2 = raw8885step1 := by apply Matrix.ext; unfold raw8885step2 raw8885step1; decide +kernel
      have hl : raw8885step1Labels = labelEmbedding1 ∘ raw8885step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8885step1 raw8885step1Labels raw8885step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2401 node2401Labels := by rfl

def raw8886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw8886Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw8886step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8886step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8886step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8886step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8886 raw8886Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw8886 raw8886Labels = mixedMoment B raw8886step0 raw8886step0Labels := by
      have hz : ∀ j, raw8886 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8886step0 = (fun i j => raw8886 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8886step0 raw8886; decide +kernel
      have hl : raw8886step0Labels = raw8886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8886 raw8886Labels permutation265 hz
    mixedMoment B raw8886step0 raw8886step0Labels = mixedMoment B raw8886step1 raw8886step1Labels := by
      have ha : raw8886step1 = (fun i j => raw8886step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8886step1 raw8886step0; decide +kernel
      have hl : raw8886step1Labels = raw8886step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8886step0 raw8886step0Labels permutation125 permutation5
    mixedMoment B raw8886step1 raw8886step1Labels = mixedMoment B raw8886step2 raw8886step2Labels := by
      have ha : raw8886step2 = raw8886step1 := by apply Matrix.ext; unfold raw8886step2 raw8886step1; decide +kernel
      have hl : raw8886step1Labels = labelEmbedding1 ∘ raw8886step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8886step1 raw8886step1Labels raw8886step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw8887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8887Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8887step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw8887step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw8887step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8887step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw8887step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8887 raw8887Labels = mixedMoment B node3283 node3283Labels := by
  calc
    mixedMoment B raw8887 raw8887Labels = mixedMoment B raw8887step0 raw8887step0Labels := by
      have hz : ∀ j, raw8887 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8887step0 = (fun i j => raw8887 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8887step0 raw8887; decide +kernel
      have hl : raw8887step0Labels = raw8887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8887 raw8887Labels permutation265 hz
    mixedMoment B raw8887step0 raw8887step0Labels = mixedMoment B raw8887step1 raw8887step1Labels := by
      have ha : raw8887step1 = (fun i j => raw8887step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8887step1 raw8887step0; decide +kernel
      have hl : raw8887step1Labels = raw8887step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8887step0 raw8887step0Labels permutation32 permutation5
    mixedMoment B raw8887step1 raw8887step1Labels = mixedMoment B raw8887step2 raw8887step2Labels := by
      have ha : raw8887step2 = -raw8887step1 := by apply Matrix.ext; change ∀ i j, raw8887step2 i j = -(raw8887step1 i j); unfold raw8887step2 raw8887step1; decide +kernel
      have hl : raw8887step2Labels = raw8887step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8887step2 raw8887step2Labels = mixedMoment B raw8887step3 raw8887step3Labels := by
      have ha : raw8887step3 = raw8887step2 := by apply Matrix.ext; unfold raw8887step3 raw8887step2; decide +kernel
      have hl : raw8887step2Labels = labelEmbedding1 ∘ raw8887step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8887step2 raw8887step2Labels raw8887step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3283 node3283Labels := by rfl

def raw8888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8888Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8888step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8888 raw8888Labels = mixedMoment B node3350 node3350Labels := by
  calc
    mixedMoment B raw8888 raw8888Labels = mixedMoment B raw8888step0 raw8888step0Labels := by
      have ha : raw8888step0 = (fun i j => raw8888 (permutation682 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8888step0 raw8888; decide +kernel
      have hl : raw8888step0Labels = raw8888Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8888 raw8888Labels permutation682 permutation5
    mixedMoment B raw8888step0 raw8888step0Labels = mixedMoment B raw8888step1 raw8888step1Labels := by
      have ha : raw8888step1 = raw8888step0 := by apply Matrix.ext; unfold raw8888step1 raw8888step0; decide +kernel
      have hl : raw8888step0Labels = labelEmbedding1 ∘ raw8888step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8888step0 raw8888step0Labels raw8888step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3350 node3350Labels := by rfl

def raw8889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8889Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8889step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8889step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8889 raw8889Labels = mixedMoment B node3355 node3355Labels := by
  calc
    mixedMoment B raw8889 raw8889Labels = mixedMoment B raw8889step0 raw8889step0Labels := by
      have hz : ∀ j, raw8889 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8889step0 = (fun i j => raw8889 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8889step0 raw8889; decide +kernel
      have hl : raw8889step0Labels = raw8889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8889 raw8889Labels permutation265 hz
    mixedMoment B raw8889step0 raw8889step0Labels = mixedMoment B raw8889step1 raw8889step1Labels := by
      have ha : raw8889step1 = (fun i j => raw8889step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8889step1 raw8889step0; decide +kernel
      have hl : raw8889step1Labels = raw8889step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8889step0 raw8889step0Labels permutation150 permutation5
    mixedMoment B raw8889step1 raw8889step1Labels = mixedMoment B raw8889step2 raw8889step2Labels := by
      have ha : raw8889step2 = raw8889step1 := by apply Matrix.ext; unfold raw8889step2 raw8889step1; decide +kernel
      have hl : raw8889step1Labels = labelEmbedding1 ∘ raw8889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8889step1 raw8889step1Labels raw8889step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3355 node3355Labels := by rfl

def raw8890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8890Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8890step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8890step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8890 raw8890Labels = mixedMoment B node3355 node3355Labels := by
  calc
    mixedMoment B raw8890 raw8890Labels = mixedMoment B raw8890step0 raw8890step0Labels := by
      have hz : ∀ j, raw8890 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8890step0 = (fun i j => raw8890 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8890step0 raw8890; decide +kernel
      have hl : raw8890step0Labels = raw8890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8890 raw8890Labels permutation265 hz
    mixedMoment B raw8890step0 raw8890step0Labels = mixedMoment B raw8890step1 raw8890step1Labels := by
      have ha : raw8890step1 = (fun i j => raw8890step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8890step1 raw8890step0; decide +kernel
      have hl : raw8890step1Labels = raw8890step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8890step0 raw8890step0Labels permutation148 permutation5
    mixedMoment B raw8890step1 raw8890step1Labels = mixedMoment B raw8890step2 raw8890step2Labels := by
      have ha : raw8890step2 = raw8890step1 := by apply Matrix.ext; unfold raw8890step2 raw8890step1; decide +kernel
      have hl : raw8890step1Labels = labelEmbedding1 ∘ raw8890step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8890step1 raw8890step1Labels raw8890step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3355 node3355Labels := by rfl

def raw8891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw8891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw8891step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8891step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8891step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8891 raw8891Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw8891 raw8891Labels = mixedMoment B raw8891step0 raw8891step0Labels := by
      have hz : ∀ j, raw8891 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8891step0 = (fun i j => raw8891 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8891step0 raw8891; decide +kernel
      have hl : raw8891step0Labels = raw8891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8891 raw8891Labels permutation265 hz
    mixedMoment B raw8891step0 raw8891step0Labels = mixedMoment B raw8891step1 raw8891step1Labels := by
      have ha : raw8891step1 = (fun i j => raw8891step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8891step1 raw8891step0; decide +kernel
      have hl : raw8891step1Labels = raw8891step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8891step0 raw8891step0Labels permutation149 permutation5
    mixedMoment B raw8891step1 raw8891step1Labels = mixedMoment B raw8891step2 raw8891step2Labels := by
      have ha : raw8891step2 = raw8891step1 := by apply Matrix.ext; unfold raw8891step2 raw8891step1; decide +kernel
      have hl : raw8891step1Labels = labelEmbedding1 ∘ raw8891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8891step1 raw8891step1Labels raw8891step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw8892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8892 raw8892Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw8892 raw8892Labels = mixedMoment B raw8892step0 raw8892step0Labels := by
      have hz : ∀ j, raw8892 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8892step0 = (fun i j => raw8892 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8892step0 raw8892; decide +kernel
      have hl : raw8892step0Labels = raw8892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8892 raw8892Labels permutation265 hz
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw8893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8893 raw8893Labels = mixedMoment B node3846 node3846Labels := by
  calc
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw8894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8894 raw8894Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw8894 raw8894Labels = mixedMoment B raw8894step0 raw8894step0Labels := by
      have hz : ∀ j, raw8894 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8894step0 = (fun i j => raw8894 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8894step0 raw8894; decide +kernel
      have hl : raw8894step0Labels = raw8894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8894 raw8894Labels permutation265 hz
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw8895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8895 raw8895Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw8895 raw8895Labels = mixedMoment B raw8895step0 raw8895step0Labels := by
      have hz : ∀ j, raw8895 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8895step0 = (fun i j => raw8895 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8895step0 raw8895; decide +kernel
      have hl : raw8895step0Labels = raw8895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8895 raw8895Labels permutation265 hz
    mixedMoment B raw8895step0 raw8895step0Labels = mixedMoment B raw8895step1 raw8895step1Labels := by
      have ha : raw8895step1 = (fun i j => raw8895step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8895step1 raw8895step0; decide +kernel
      have hl : raw8895step1Labels = raw8895step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8895step0 raw8895step0Labels permutation38 permutation2
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw8896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw8896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8896 raw8896Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw8896 raw8896Labels = mixedMoment B raw8896step0 raw8896step0Labels := by
      have hz : ∀ j, raw8896 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8896step0 = (fun i j => raw8896 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8896step0 raw8896; decide +kernel
      have hl : raw8896step0Labels = raw8896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8896 raw8896Labels permutation265 hz
    mixedMoment B raw8896step0 raw8896step0Labels = mixedMoment B raw8896step1 raw8896step1Labels := by
      have ha : raw8896step1 = (fun i j => raw8896step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8896step1 raw8896step0; decide +kernel
      have hl : raw8896step1Labels = raw8896step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8896step0 raw8896step0Labels permutation44 permutation2
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw8897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8897 raw8897Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw8897 raw8897Labels = mixedMoment B raw8897step0 raw8897step0Labels := by
      have hz : ∀ j, raw8897 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8897step0 = (fun i j => raw8897 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8897step0 raw8897; decide +kernel
      have hl : raw8897step0Labels = raw8897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8897 raw8897Labels permutation265 hz
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw8898 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]
def raw8898Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8898step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]
def raw8898step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8898step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw8898step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical8898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8898 raw8898Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw8898 raw8898Labels = mixedMoment B raw8898step0 raw8898step0Labels := by
      have hz : ∀ j, raw8898 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8898step0 = (fun i j => raw8898 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8898step0 raw8898; decide +kernel
      have hl : raw8898step0Labels = raw8898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8898 raw8898Labels permutation265 hz
    mixedMoment B raw8898step0 raw8898step0Labels = mixedMoment B raw8898step1 raw8898step1Labels := by
      have ha : raw8898step1 = (fun i j => raw8898step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8898step1 raw8898step0; decide +kernel
      have hl : raw8898step1Labels = raw8898step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8898step0 raw8898step0Labels permutation44 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw8899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8899 raw8899Labels = mixedMoment B node1247 node1247Labels := by
  calc
    mixedMoment B raw8899 raw8899Labels = mixedMoment B raw8899step0 raw8899step0Labels := by
      have ha : raw8899step0 = (fun i j => raw8899 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8899step0 raw8899; decide +kernel
      have hl : raw8899step0Labels = raw8899Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8899 raw8899Labels permutation184 permutation2
    _ = mixedMoment B node1247 node1247Labels := by rfl

def raw8900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8900 raw8900Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw8900 raw8900Labels = mixedMoment B raw8900step0 raw8900step0Labels := by
      have hz : ∀ j, raw8900 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8900step0 = (fun i j => raw8900 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8900step0 raw8900; decide +kernel
      have hl : raw8900step0Labels = raw8900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8900 raw8900Labels permutation265 hz
    mixedMoment B raw8900step0 raw8900step0Labels = mixedMoment B raw8900step1 raw8900step1Labels := by
      have ha : raw8900step1 = (fun i j => raw8900step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8900step1 raw8900step0; decide +kernel
      have hl : raw8900step1Labels = raw8900step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8900step0 raw8900step0Labels permutation40 permutation2
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw8901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8901 raw8901Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw8901 raw8901Labels = mixedMoment B raw8901step0 raw8901step0Labels := by
      have hz : ∀ j, raw8901 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8901step0 = (fun i j => raw8901 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8901step0 raw8901; decide +kernel
      have hl : raw8901step0Labels = raw8901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8901 raw8901Labels permutation265 hz
    mixedMoment B raw8901step0 raw8901step0Labels = mixedMoment B raw8901step1 raw8901step1Labels := by
      have ha : raw8901step1 = (fun i j => raw8901step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8901step1 raw8901step0; decide +kernel
      have hl : raw8901step1Labels = raw8901step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8901step0 raw8901step0Labels permutation34 permutation2
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw8902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8902 raw8902Labels = mixedMoment B node1253 node1253Labels := by
  calc
    mixedMoment B raw8902 raw8902Labels = mixedMoment B raw8902step0 raw8902step0Labels := by
      have hz : ∀ j, raw8902 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8902step0 = (fun i j => raw8902 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8902step0 raw8902; decide +kernel
      have hl : raw8902step0Labels = raw8902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8902 raw8902Labels permutation265 hz
    _ = mixedMoment B node1253 node1253Labels := by rfl

def raw8903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8903 raw8903Labels = mixedMoment B node1249 node1249Labels := by
  calc
    mixedMoment B raw8903 raw8903Labels = mixedMoment B raw8903step0 raw8903step0Labels := by
      have hz : ∀ j, raw8903 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8903step0 = (fun i j => raw8903 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8903step0 raw8903; decide +kernel
      have hl : raw8903step0Labels = raw8903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8903 raw8903Labels permutation265 hz
    _ = mixedMoment B node1249 node1249Labels := by rfl

def raw8904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8904 raw8904Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw8904 raw8904Labels = mixedMoment B raw8904step0 raw8904step0Labels := by
      have ha : raw8904step0 = (fun i j => raw8904 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8904step0 raw8904; decide +kernel
      have hl : raw8904step0Labels = raw8904Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8904 raw8904Labels permutation160 permutation2
    _ = mixedMoment B node2567 node2567Labels := by rfl

def raw8905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8905 raw8905Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw8905 raw8905Labels = mixedMoment B raw8905step0 raw8905step0Labels := by
      have ha : raw8905step0 = (fun i j => raw8905 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8905step0 raw8905; decide +kernel
      have hl : raw8905step0Labels = raw8905Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8905 raw8905Labels permutation154 permutation2
    _ = mixedMoment B node2567 node2567Labels := by rfl

def raw8906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8906 raw8906Labels = mixedMoment B node2564 node2564Labels := by
  calc
    _ = mixedMoment B node2564 node2564Labels := by rfl

def raw8907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8907 raw8907Labels = mixedMoment B node2562 node2562Labels := by
  calc
    _ = mixedMoment B node2562 node2562Labels := by rfl

def raw8908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8908 raw8908Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw8908 raw8908Labels = mixedMoment B raw8908step0 raw8908step0Labels := by
      have hz : ∀ j, raw8908 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8908step0 = (fun i j => raw8908 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8908step0 raw8908; decide +kernel
      have hl : raw8908step0Labels = raw8908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8908 raw8908Labels permutation265 hz
    mixedMoment B raw8908step0 raw8908step0Labels = mixedMoment B raw8908step1 raw8908step1Labels := by
      have ha : raw8908step1 = (fun i j => raw8908step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8908step1 raw8908step0; decide +kernel
      have hl : raw8908step1Labels = raw8908step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8908step0 raw8908step0Labels permutation40 permutation2
    _ = mixedMoment B node2633 node2633Labels := by rfl

def raw8909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8909 raw8909Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw8909 raw8909Labels = mixedMoment B raw8909step0 raw8909step0Labels := by
      have hz : ∀ j, raw8909 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8909step0 = (fun i j => raw8909 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8909step0 raw8909; decide +kernel
      have hl : raw8909step0Labels = raw8909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8909 raw8909Labels permutation265 hz
    mixedMoment B raw8909step0 raw8909step0Labels = mixedMoment B raw8909step1 raw8909step1Labels := by
      have ha : raw8909step1 = (fun i j => raw8909step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8909step1 raw8909step0; decide +kernel
      have hl : raw8909step1Labels = raw8909step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8909step0 raw8909step0Labels permutation46 permutation2
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw8910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8910 raw8910Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw8910 raw8910Labels = mixedMoment B raw8910step0 raw8910step0Labels := by
      have hz : ∀ j, raw8910 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8910step0 = (fun i j => raw8910 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8910step0 raw8910; decide +kernel
      have hl : raw8910step0Labels = raw8910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8910 raw8910Labels permutation265 hz
    mixedMoment B raw8910step0 raw8910step0Labels = mixedMoment B raw8910step1 raw8910step1Labels := by
      have ha : raw8910step1 = (fun i j => raw8910step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8910step1 raw8910step0; decide +kernel
      have hl : raw8910step1Labels = raw8910step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8910step0 raw8910step0Labels permutation40 permutation2
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw8911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8911 raw8911Labels = mixedMoment B node2622 node2622Labels := by
  calc
    mixedMoment B raw8911 raw8911Labels = mixedMoment B raw8911step0 raw8911step0Labels := by
      have ha : raw8911step0 = (fun i j => raw8911 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8911step0 raw8911; decide +kernel
      have hl : raw8911step0Labels = raw8911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8911 raw8911Labels permutation184 permutation2
    _ = mixedMoment B node2622 node2622Labels := by rfl

def raw8912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8912 raw8912Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw8912 raw8912Labels = mixedMoment B raw8912step0 raw8912step0Labels := by
      have hz : ∀ j, raw8912 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8912step0 = (fun i j => raw8912 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8912step0 raw8912; decide +kernel
      have hl : raw8912step0Labels = raw8912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8912 raw8912Labels permutation265 hz
    mixedMoment B raw8912step0 raw8912step0Labels = mixedMoment B raw8912step1 raw8912step1Labels := by
      have ha : raw8912step1 = (fun i j => raw8912step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8912step1 raw8912step0; decide +kernel
      have hl : raw8912step1Labels = raw8912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8912step0 raw8912step0Labels permutation34 permutation2
    _ = mixedMoment B node2633 node2633Labels := by rfl

def raw8913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8913 raw8913Labels = mixedMoment B node2627 node2627Labels := by
  calc
    mixedMoment B raw8913 raw8913Labels = mixedMoment B raw8913step0 raw8913step0Labels := by
      have hz : ∀ j, raw8913 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8913step0 = (fun i j => raw8913 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8913step0 raw8913; decide +kernel
      have hl : raw8913step0Labels = raw8913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8913 raw8913Labels permutation265 hz
    _ = mixedMoment B node2627 node2627Labels := by rfl

def raw8914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8914 raw8914Labels = mixedMoment B node2624 node2624Labels := by
  calc
    mixedMoment B raw8914 raw8914Labels = mixedMoment B raw8914step0 raw8914step0Labels := by
      have hz : ∀ j, raw8914 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8914step0 = (fun i j => raw8914 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8914step0 raw8914; decide +kernel
      have hl : raw8914step0Labels = raw8914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8914 raw8914Labels permutation265 hz
    _ = mixedMoment B node2624 node2624Labels := by rfl

def raw8915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8915 raw8915Labels = mixedMoment B node2627 node2627Labels := by
  calc
    mixedMoment B raw8915 raw8915Labels = mixedMoment B raw8915step0 raw8915step0Labels := by
      have hz : ∀ j, raw8915 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8915step0 = (fun i j => raw8915 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8915step0 raw8915; decide +kernel
      have hl : raw8915step0Labels = raw8915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8915 raw8915Labels permutation265 hz
    mixedMoment B raw8915step0 raw8915step0Labels = mixedMoment B raw8915step1 raw8915step1Labels := by
      have ha : raw8915step1 = (fun i j => raw8915step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8915step1 raw8915step0; decide +kernel
      have hl : raw8915step1Labels = raw8915step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8915step0 raw8915step0Labels permutation38 permutation2
    _ = mixedMoment B node2627 node2627Labels := by rfl

def raw8916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw8916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw8916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw8916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8916 raw8916Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw8916 raw8916Labels = mixedMoment B raw8916step0 raw8916step0Labels := by
      have hz : ∀ j, raw8916 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8916step0 = (fun i j => raw8916 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8916step0 raw8916; decide +kernel
      have hl : raw8916step0Labels = raw8916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8916 raw8916Labels permutation265 hz
    mixedMoment B raw8916step0 raw8916step0Labels = mixedMoment B raw8916step1 raw8916step1Labels := by
      have ha : raw8916step1 = (fun i j => raw8916step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8916step1 raw8916step0; decide +kernel
      have hl : raw8916step1Labels = raw8916step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8916step0 raw8916step0Labels permutation33 permutation2
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw8917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8917step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8917 raw8917Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw8917 raw8917Labels = mixedMoment B raw8917step0 raw8917step0Labels := by
      have ha : raw8917step0 = (fun i j => raw8917 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8917step0 raw8917; decide +kernel
      have hl : raw8917step0Labels = raw8917Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8917 raw8917Labels permutation682 permutation2
    mixedMoment B raw8917step0 raw8917step0Labels = mixedMoment B raw8917step1 raw8917step1Labels := by
      have ha : raw8917step1 = -raw8917step0 := by apply Matrix.ext; change ∀ i j, raw8917step1 i j = -(raw8917step0 i j); unfold raw8917step1 raw8917step0; decide +kernel
      have hl : raw8917step1Labels = raw8917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw8918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8918step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8918step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8918 raw8918Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw8918 raw8918Labels = mixedMoment B raw8918step0 raw8918step0Labels := by
      have hz : ∀ j, raw8918 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8918step0 = (fun i j => raw8918 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8918step0 raw8918; decide +kernel
      have hl : raw8918step0Labels = raw8918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8918 raw8918Labels permutation265 hz
    mixedMoment B raw8918step0 raw8918step0Labels = mixedMoment B raw8918step1 raw8918step1Labels := by
      have ha : raw8918step1 = (fun i j => raw8918step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8918step1 raw8918step0; decide +kernel
      have hl : raw8918step1Labels = raw8918step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8918step0 raw8918step0Labels permutation151 permutation2
    mixedMoment B raw8918step1 raw8918step1Labels = mixedMoment B raw8918step2 raw8918step2Labels := by
      have ha : raw8918step2 = -raw8918step1 := by apply Matrix.ext; change ∀ i j, raw8918step2 i j = -(raw8918step1 i j); unfold raw8918step2 raw8918step1; decide +kernel
      have hl : raw8918step2Labels = raw8918step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw8919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8919step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8919step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8919 raw8919Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw8919 raw8919Labels = mixedMoment B raw8919step0 raw8919step0Labels := by
      have hz : ∀ j, raw8919 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8919step0 = (fun i j => raw8919 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8919step0 raw8919; decide +kernel
      have hl : raw8919step0Labels = raw8919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8919 raw8919Labels permutation265 hz
    mixedMoment B raw8919step0 raw8919step0Labels = mixedMoment B raw8919step1 raw8919step1Labels := by
      have ha : raw8919step1 = (fun i j => raw8919step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8919step1 raw8919step0; decide +kernel
      have hl : raw8919step1Labels = raw8919step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8919step0 raw8919step0Labels permutation149 permutation2
    mixedMoment B raw8919step1 raw8919step1Labels = mixedMoment B raw8919step2 raw8919step2Labels := by
      have ha : raw8919step2 = -raw8919step1 := by apply Matrix.ext; change ∀ i j, raw8919step2 i j = -(raw8919step1 i j); unfold raw8919step2 raw8919step1; decide +kernel
      have hl : raw8919step2Labels = raw8919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw8920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw8920step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8920step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8920step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8920step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8920 raw8920Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw8920 raw8920Labels = mixedMoment B raw8920step0 raw8920step0Labels := by
      have hz : ∀ j, raw8920 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8920step0 = (fun i j => raw8920 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8920step0 raw8920; decide +kernel
      have hl : raw8920step0Labels = raw8920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8920 raw8920Labels permutation265 hz
    mixedMoment B raw8920step0 raw8920step0Labels = mixedMoment B raw8920step1 raw8920step1Labels := by
      have ha : raw8920step1 = (fun i j => raw8920step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8920step1 raw8920step0; decide +kernel
      have hl : raw8920step1Labels = raw8920step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8920step0 raw8920step0Labels permutation108 permutation4
    mixedMoment B raw8920step1 raw8920step1Labels = mixedMoment B raw8920step2 raw8920step2Labels := by
      have ha : raw8920step2 = -raw8920step1 := by apply Matrix.ext; change ∀ i j, raw8920step2 i j = -(raw8920step1 i j); unfold raw8920step2 raw8920step1; decide +kernel
      have hl : raw8920step2Labels = raw8920step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8920step2 raw8920step2Labels = mixedMoment B raw8920step3 raw8920step3Labels := by
      have ha : raw8920step3 = raw8920step2 := by apply Matrix.ext; unfold raw8920step3 raw8920step2; decide +kernel
      have hl : raw8920step2Labels = labelEmbedding7 ∘ raw8920step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8920step2 raw8920step2Labels raw8920step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw8921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8921step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8921step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8921 raw8921Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw8921 raw8921Labels = mixedMoment B raw8921step0 raw8921step0Labels := by
      have hz : ∀ j, raw8921 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8921step0 = (fun i j => raw8921 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8921step0 raw8921; decide +kernel
      have hl : raw8921step0Labels = raw8921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8921 raw8921Labels permutation265 hz
    mixedMoment B raw8921step0 raw8921step0Labels = mixedMoment B raw8921step1 raw8921step1Labels := by
      have ha : raw8921step1 = (fun i j => raw8921step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8921step1 raw8921step0; decide +kernel
      have hl : raw8921step1Labels = raw8921step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8921step0 raw8921step0Labels permutation125 permutation7
    mixedMoment B raw8921step1 raw8921step1Labels = mixedMoment B raw8921step2 raw8921step2Labels := by
      have ha : raw8921step2 = raw8921step1 := by apply Matrix.ext; unfold raw8921step2 raw8921step1; decide +kernel
      have hl : raw8921step1Labels = labelEmbedding10 ∘ raw8921step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8921step1 raw8921step1Labels raw8921step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw8922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8922step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8922step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8922 raw8922Labels = mixedMoment B node4436 node4436Labels := by
  calc
    mixedMoment B raw8922 raw8922Labels = mixedMoment B raw8922step0 raw8922step0Labels := by
      have ha : raw8922step0 = (fun i j => raw8922 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8922step0 raw8922; decide +kernel
      have hl : raw8922step0Labels = raw8922Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8922 raw8922Labels permutation184 permutation3
    mixedMoment B raw8922step0 raw8922step0Labels = mixedMoment B raw8922step1 raw8922step1Labels := by
      have ha : raw8922step1 = raw8922step0 := by apply Matrix.ext; unfold raw8922step1 raw8922step0; decide +kernel
      have hl : raw8922step0Labels = labelEmbedding6 ∘ raw8922step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8922step0 raw8922step0Labels raw8922step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4436 node4436Labels := by rfl

def raw8923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8923step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8923step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8923 raw8923Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw8923 raw8923Labels = mixedMoment B raw8923step0 raw8923step0Labels := by
      have ha : raw8923step0 = (fun i j => raw8923 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8923step0 raw8923; decide +kernel
      have hl : raw8923step0Labels = raw8923Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8923 raw8923Labels permutation184 permutation3
    mixedMoment B raw8923step0 raw8923step0Labels = mixedMoment B raw8923step1 raw8923step1Labels := by
      have ha : raw8923step1 = raw8923step0 := by apply Matrix.ext; unfold raw8923step1 raw8923step0; decide +kernel
      have hl : raw8923step0Labels = labelEmbedding6 ∘ raw8923step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8923step0 raw8923step0Labels raw8923step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw8924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8924step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8924step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8924 raw8924Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw8924 raw8924Labels = mixedMoment B raw8924step0 raw8924step0Labels := by
      have ha : raw8924step0 = (fun i j => raw8924 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8924step0 raw8924; decide +kernel
      have hl : raw8924step0Labels = raw8924Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8924 raw8924Labels permutation208 permutation3
    mixedMoment B raw8924step0 raw8924step0Labels = mixedMoment B raw8924step1 raw8924step1Labels := by
      have ha : raw8924step1 = raw8924step0 := by apply Matrix.ext; unfold raw8924step1 raw8924step0; decide +kernel
      have hl : raw8924step0Labels = labelEmbedding6 ∘ raw8924step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8924step0 raw8924step0Labels raw8924step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw8925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8925step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8925 raw8925Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw8925 raw8925Labels = mixedMoment B raw8925step0 raw8925step0Labels := by
      have ha : raw8925step0 = (fun i j => raw8925 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8925step0 raw8925; decide +kernel
      have hl : raw8925step0Labels = raw8925Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8925 raw8925Labels permutation232 permutation3
    mixedMoment B raw8925step0 raw8925step0Labels = mixedMoment B raw8925step1 raw8925step1Labels := by
      have ha : raw8925step1 = raw8925step0 := by apply Matrix.ext; unfold raw8925step1 raw8925step0; decide +kernel
      have hl : raw8925step0Labels = labelEmbedding6 ∘ raw8925step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8925step0 raw8925step0Labels raw8925step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

def raw8926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8926step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8926 raw8926Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw8926 raw8926Labels = mixedMoment B raw8926step0 raw8926step0Labels := by
      have ha : raw8926step0 = (fun i j => raw8926 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8926step0 raw8926; decide +kernel
      have hl : raw8926step0Labels = raw8926Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8926 raw8926Labels permutation185 permutation3
    mixedMoment B raw8926step0 raw8926step0Labels = mixedMoment B raw8926step1 raw8926step1Labels := by
      have ha : raw8926step1 = raw8926step0 := by apply Matrix.ext; unfold raw8926step1 raw8926step0; decide +kernel
      have hl : raw8926step0Labels = labelEmbedding6 ∘ raw8926step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8926step0 raw8926step0Labels raw8926step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw8927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8927step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8927 raw8927Labels = mixedMoment B node4453 node4453Labels := by
  calc
    mixedMoment B raw8927 raw8927Labels = mixedMoment B raw8927step0 raw8927step0Labels := by
      have hz : ∀ j, raw8927 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8927step0 = (fun i j => raw8927 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8927step0 raw8927; decide +kernel
      have hl : raw8927step0Labels = raw8927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8927 raw8927Labels permutation265 hz
    mixedMoment B raw8927step0 raw8927step0Labels = mixedMoment B raw8927step1 raw8927step1Labels := by
      have ha : raw8927step1 = (fun i j => raw8927step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8927step1 raw8927step0; decide +kernel
      have hl : raw8927step1Labels = raw8927step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8927step0 raw8927step0Labels permutation40 permutation3
    mixedMoment B raw8927step1 raw8927step1Labels = mixedMoment B raw8927step2 raw8927step2Labels := by
      have ha : raw8927step2 = raw8927step1 := by apply Matrix.ext; unfold raw8927step2 raw8927step1; decide +kernel
      have hl : raw8927step1Labels = labelEmbedding6 ∘ raw8927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8927step1 raw8927step1Labels raw8927step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4453 node4453Labels := by rfl

def raw8928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8928step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8928step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8928 raw8928Labels = mixedMoment B node5071 node5071Labels := by
  calc
    mixedMoment B raw8928 raw8928Labels = mixedMoment B raw8928step0 raw8928step0Labels := by
      have ha : raw8928step0 = (fun i j => raw8928 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8928step0 raw8928; decide +kernel
      have hl : raw8928step0Labels = raw8928Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8928 raw8928Labels permutation160 permutation3
    mixedMoment B raw8928step0 raw8928step0Labels = mixedMoment B raw8928step1 raw8928step1Labels := by
      have ha : raw8928step1 = raw8928step0 := by apply Matrix.ext; unfold raw8928step1 raw8928step0; decide +kernel
      have hl : raw8928step0Labels = labelEmbedding6 ∘ raw8928step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8928step0 raw8928step0Labels raw8928step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5071 node5071Labels := by rfl

def raw8929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8929step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8929step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8929step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8929 raw8929Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw8929 raw8929Labels = mixedMoment B raw8929step0 raw8929step0Labels := by
      have hz : ∀ j, raw8929 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8929step0 = (fun i j => raw8929 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8929step0 raw8929; decide +kernel
      have hl : raw8929step0Labels = raw8929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8929 raw8929Labels permutation265 hz
    mixedMoment B raw8929step0 raw8929step0Labels = mixedMoment B raw8929step1 raw8929step1Labels := by
      have ha : raw8929step1 = (fun i j => raw8929step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8929step1 raw8929step0; decide +kernel
      have hl : raw8929step1Labels = raw8929step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8929step0 raw8929step0Labels permutation40 permutation3
    mixedMoment B raw8929step1 raw8929step1Labels = mixedMoment B raw8929step2 raw8929step2Labels := by
      have ha : raw8929step2 = raw8929step1 := by apply Matrix.ext; unfold raw8929step2 raw8929step1; decide +kernel
      have hl : raw8929step1Labels = labelEmbedding6 ∘ raw8929step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8929step1 raw8929step1Labels raw8929step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw8930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8930step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8930step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8930 raw8930Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw8930 raw8930Labels = mixedMoment B raw8930step0 raw8930step0Labels := by
      have hz : ∀ j, raw8930 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8930step0 = (fun i j => raw8930 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8930step0 raw8930; decide +kernel
      have hl : raw8930step0Labels = raw8930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8930 raw8930Labels permutation265 hz
    mixedMoment B raw8930step0 raw8930step0Labels = mixedMoment B raw8930step1 raw8930step1Labels := by
      have ha : raw8930step1 = (fun i j => raw8930step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8930step1 raw8930step0; decide +kernel
      have hl : raw8930step1Labels = raw8930step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8930step0 raw8930step0Labels permutation46 permutation3
    mixedMoment B raw8930step1 raw8930step1Labels = mixedMoment B raw8930step2 raw8930step2Labels := by
      have ha : raw8930step2 = raw8930step1 := by apply Matrix.ext; unfold raw8930step2 raw8930step1; decide +kernel
      have hl : raw8930step1Labels = labelEmbedding6 ∘ raw8930step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8930step1 raw8930step1Labels raw8930step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw8931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8931step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8931step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8931 raw8931Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw8931 raw8931Labels = mixedMoment B raw8931step0 raw8931step0Labels := by
      have hz : ∀ j, raw8931 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8931step0 = (fun i j => raw8931 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8931step0 raw8931; decide +kernel
      have hl : raw8931step0Labels = raw8931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8931 raw8931Labels permutation265 hz
    mixedMoment B raw8931step0 raw8931step0Labels = mixedMoment B raw8931step1 raw8931step1Labels := by
      have ha : raw8931step1 = (fun i j => raw8931step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8931step1 raw8931step0; decide +kernel
      have hl : raw8931step1Labels = raw8931step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8931step0 raw8931step0Labels permutation41 permutation3
    mixedMoment B raw8931step1 raw8931step1Labels = mixedMoment B raw8931step2 raw8931step2Labels := by
      have ha : raw8931step2 = raw8931step1 := by apply Matrix.ext; unfold raw8931step2 raw8931step1; decide +kernel
      have hl : raw8931step1Labels = labelEmbedding6 ∘ raw8931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8931step1 raw8931step1Labels raw8931step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw8932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8932step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8932 raw8932Labels = mixedMoment B node4453 node4453Labels := by
  calc
    mixedMoment B raw8932 raw8932Labels = mixedMoment B raw8932step0 raw8932step0Labels := by
      have hz : ∀ j, raw8932 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8932step0 = (fun i j => raw8932 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8932step0 raw8932; decide +kernel
      have hl : raw8932step0Labels = raw8932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8932 raw8932Labels permutation265 hz
    mixedMoment B raw8932step0 raw8932step0Labels = mixedMoment B raw8932step1 raw8932step1Labels := by
      have ha : raw8932step1 = (fun i j => raw8932step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8932step1 raw8932step0; decide +kernel
      have hl : raw8932step1Labels = raw8932step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8932step0 raw8932step0Labels permutation34 permutation3
    mixedMoment B raw8932step1 raw8932step1Labels = mixedMoment B raw8932step2 raw8932step2Labels := by
      have ha : raw8932step2 = raw8932step1 := by apply Matrix.ext; unfold raw8932step2 raw8932step1; decide +kernel
      have hl : raw8932step1Labels = labelEmbedding6 ∘ raw8932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8932step1 raw8932step1Labels raw8932step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4453 node4453Labels := by rfl

def raw8933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8933step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8933 raw8933Labels = mixedMoment B node5071 node5071Labels := by
  calc
    mixedMoment B raw8933 raw8933Labels = mixedMoment B raw8933step0 raw8933step0Labels := by
      have ha : raw8933step0 = (fun i j => raw8933 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8933step0 raw8933; decide +kernel
      have hl : raw8933step0Labels = raw8933Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8933 raw8933Labels permutation154 permutation3
    mixedMoment B raw8933step0 raw8933step0Labels = mixedMoment B raw8933step1 raw8933step1Labels := by
      have ha : raw8933step1 = raw8933step0 := by apply Matrix.ext; unfold raw8933step1 raw8933step0; decide +kernel
      have hl : raw8933step0Labels = labelEmbedding6 ∘ raw8933step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8933step0 raw8933step0Labels raw8933step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5071 node5071Labels := by rfl

def raw8934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8934step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8934step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8934step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8934 raw8934Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw8934 raw8934Labels = mixedMoment B raw8934step0 raw8934step0Labels := by
      have hz : ∀ j, raw8934 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8934step0 = (fun i j => raw8934 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8934step0 raw8934; decide +kernel
      have hl : raw8934step0Labels = raw8934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8934 raw8934Labels permutation265 hz
    mixedMoment B raw8934step0 raw8934step0Labels = mixedMoment B raw8934step1 raw8934step1Labels := by
      have ha : raw8934step1 = (fun i j => raw8934step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8934step1 raw8934step0; decide +kernel
      have hl : raw8934step1Labels = raw8934step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8934step0 raw8934step0Labels permutation34 permutation3
    mixedMoment B raw8934step1 raw8934step1Labels = mixedMoment B raw8934step2 raw8934step2Labels := by
      have ha : raw8934step2 = raw8934step1 := by apply Matrix.ext; unfold raw8934step2 raw8934step1; decide +kernel
      have hl : raw8934step1Labels = labelEmbedding6 ∘ raw8934step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8934step1 raw8934step1Labels raw8934step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw8935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8935step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8935step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8935 raw8935Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw8935 raw8935Labels = mixedMoment B raw8935step0 raw8935step0Labels := by
      have hz : ∀ j, raw8935 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8935step0 = (fun i j => raw8935 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8935step0 raw8935; decide +kernel
      have hl : raw8935step0Labels = raw8935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8935 raw8935Labels permutation265 hz
    mixedMoment B raw8935step0 raw8935step0Labels = mixedMoment B raw8935step1 raw8935step1Labels := by
      have ha : raw8935step1 = (fun i j => raw8935step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8935step1 raw8935step0; decide +kernel
      have hl : raw8935step1Labels = raw8935step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8935step0 raw8935step0Labels permutation44 permutation3
    mixedMoment B raw8935step1 raw8935step1Labels = mixedMoment B raw8935step2 raw8935step2Labels := by
      have ha : raw8935step2 = raw8935step1 := by apply Matrix.ext; unfold raw8935step2 raw8935step1; decide +kernel
      have hl : raw8935step1Labels = labelEmbedding6 ∘ raw8935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8935step1 raw8935step1Labels raw8935step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw8936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8936step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8936 raw8936Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw8936 raw8936Labels = mixedMoment B raw8936step0 raw8936step0Labels := by
      have hz : ∀ j, raw8936 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8936step0 = (fun i j => raw8936 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8936step0 raw8936; decide +kernel
      have hl : raw8936step0Labels = raw8936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8936 raw8936Labels permutation265 hz
    mixedMoment B raw8936step0 raw8936step0Labels = mixedMoment B raw8936step1 raw8936step1Labels := by
      have ha : raw8936step1 = (fun i j => raw8936step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8936step1 raw8936step0; decide +kernel
      have hl : raw8936step1Labels = raw8936step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8936step0 raw8936step0Labels permutation35 permutation3
    mixedMoment B raw8936step1 raw8936step1Labels = mixedMoment B raw8936step2 raw8936step2Labels := by
      have ha : raw8936step2 = raw8936step1 := by apply Matrix.ext; unfold raw8936step2 raw8936step1; decide +kernel
      have hl : raw8936step1Labels = labelEmbedding6 ∘ raw8936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8936step1 raw8936step1Labels raw8936step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw8937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8937step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8937 raw8937Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw8937 raw8937Labels = mixedMoment B raw8937step0 raw8937step0Labels := by
      have hz : ∀ j, raw8937 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8937step0 = (fun i j => raw8937 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8937step0 raw8937; decide +kernel
      have hl : raw8937step0Labels = raw8937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8937 raw8937Labels permutation265 hz
    mixedMoment B raw8937step0 raw8937step0Labels = mixedMoment B raw8937step1 raw8937step1Labels := by
      have ha : raw8937step1 = (fun i j => raw8937step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8937step1 raw8937step0; decide +kernel
      have hl : raw8937step1Labels = raw8937step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8937step0 raw8937step0Labels permutation32 permutation3
    mixedMoment B raw8937step1 raw8937step1Labels = mixedMoment B raw8937step2 raw8937step2Labels := by
      have ha : raw8937step2 = raw8937step1 := by apply Matrix.ext; unfold raw8937step2 raw8937step1; decide +kernel
      have hl : raw8937step1Labels = labelEmbedding6 ∘ raw8937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8937step1 raw8937step1Labels raw8937step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw8938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8938step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8938 raw8938Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw8938 raw8938Labels = mixedMoment B raw8938step0 raw8938step0Labels := by
      have ha : raw8938step0 = (fun i j => raw8938 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8938step0 raw8938; decide +kernel
      have hl : raw8938step0Labels = raw8938Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8938 raw8938Labels permutation152 permutation3
    mixedMoment B raw8938step0 raw8938step0Labels = mixedMoment B raw8938step1 raw8938step1Labels := by
      have ha : raw8938step1 = raw8938step0 := by apply Matrix.ext; unfold raw8938step1 raw8938step0; decide +kernel
      have hl : raw8938step0Labels = labelEmbedding6 ∘ raw8938step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8938step0 raw8938step0Labels raw8938step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw8939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8939step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8939 raw8939Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw8939 raw8939Labels = mixedMoment B raw8939step0 raw8939step0Labels := by
      have hz : ∀ j, raw8939 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8939step0 = (fun i j => raw8939 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8939step0 raw8939; decide +kernel
      have hl : raw8939step0Labels = raw8939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8939 raw8939Labels permutation265 hz
    mixedMoment B raw8939step0 raw8939step0Labels = mixedMoment B raw8939step1 raw8939step1Labels := by
      have ha : raw8939step1 = (fun i j => raw8939step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8939step1 raw8939step0; decide +kernel
      have hl : raw8939step1Labels = raw8939step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8939step0 raw8939step0Labels permutation32 permutation3
    mixedMoment B raw8939step1 raw8939step1Labels = mixedMoment B raw8939step2 raw8939step2Labels := by
      have ha : raw8939step2 = raw8939step1 := by apply Matrix.ext; unfold raw8939step2 raw8939step1; decide +kernel
      have hl : raw8939step1Labels = labelEmbedding6 ∘ raw8939step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8939step1 raw8939step1Labels raw8939step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw8940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8940step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8940step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8940 raw8940Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw8940 raw8940Labels = mixedMoment B raw8940step0 raw8940step0Labels := by
      have hz : ∀ j, raw8940 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8940step0 = (fun i j => raw8940 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8940step0 raw8940; decide +kernel
      have hl : raw8940step0Labels = raw8940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8940 raw8940Labels permutation265 hz
    mixedMoment B raw8940step0 raw8940step0Labels = mixedMoment B raw8940step1 raw8940step1Labels := by
      have ha : raw8940step1 = (fun i j => raw8940step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8940step1 raw8940step0; decide +kernel
      have hl : raw8940step1Labels = raw8940step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8940step0 raw8940step0Labels permutation38 permutation3
    mixedMoment B raw8940step1 raw8940step1Labels = mixedMoment B raw8940step2 raw8940step2Labels := by
      have ha : raw8940step2 = raw8940step1 := by apply Matrix.ext; unfold raw8940step2 raw8940step1; decide +kernel
      have hl : raw8940step1Labels = labelEmbedding6 ∘ raw8940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8940step1 raw8940step1Labels raw8940step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw8941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw8941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw8941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw8941step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw8941step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8941 raw8941Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw8941 raw8941Labels = mixedMoment B raw8941step0 raw8941step0Labels := by
      have hz : ∀ j, raw8941 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8941step0 = (fun i j => raw8941 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8941step0 raw8941; decide +kernel
      have hl : raw8941step0Labels = raw8941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8941 raw8941Labels permutation265 hz
    mixedMoment B raw8941step0 raw8941step0Labels = mixedMoment B raw8941step1 raw8941step1Labels := by
      have ha : raw8941step1 = (fun i j => raw8941step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8941step1 raw8941step0; decide +kernel
      have hl : raw8941step1Labels = raw8941step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8941step0 raw8941step0Labels permutation33 permutation3
    mixedMoment B raw8941step1 raw8941step1Labels = mixedMoment B raw8941step2 raw8941step2Labels := by
      have ha : raw8941step2 = raw8941step1 := by apply Matrix.ext; unfold raw8941step2 raw8941step1; decide +kernel
      have hl : raw8941step1Labels = labelEmbedding6 ∘ raw8941step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8941step1 raw8941step1Labels raw8941step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw8942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8942step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8942step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8942 raw8942Labels = mixedMoment B node4437 node4437Labels := by
  calc
    mixedMoment B raw8942 raw8942Labels = mixedMoment B raw8942step0 raw8942step0Labels := by
      have hz : ∀ j, raw8942 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8942step0 = (fun i j => raw8942 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8942step0 raw8942; decide +kernel
      have hl : raw8942step0Labels = raw8942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8942 raw8942Labels permutation265 hz
    mixedMoment B raw8942step0 raw8942step0Labels = mixedMoment B raw8942step1 raw8942step1Labels := by
      have ha : raw8942step1 = (fun i j => raw8942step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8942step1 raw8942step0; decide +kernel
      have hl : raw8942step1Labels = raw8942step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8942step0 raw8942step0Labels permutation32 permutation3
    mixedMoment B raw8942step1 raw8942step1Labels = mixedMoment B raw8942step2 raw8942step2Labels := by
      have ha : raw8942step2 = raw8942step1 := by apply Matrix.ext; unfold raw8942step2 raw8942step1; decide +kernel
      have hl : raw8942step1Labels = labelEmbedding6 ∘ raw8942step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8942step1 raw8942step1Labels raw8942step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4437 node4437Labels := by rfl

def raw8943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8943step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8943step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8943 raw8943Labels = mixedMoment B node5064 node5064Labels := by
  calc
    mixedMoment B raw8943 raw8943Labels = mixedMoment B raw8943step0 raw8943step0Labels := by
      have ha : raw8943step0 = (fun i j => raw8943 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8943step0 raw8943; decide +kernel
      have hl : raw8943step0Labels = raw8943Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8943 raw8943Labels permutation152 permutation3
    mixedMoment B raw8943step0 raw8943step0Labels = mixedMoment B raw8943step1 raw8943step1Labels := by
      have ha : raw8943step1 = raw8943step0 := by apply Matrix.ext; unfold raw8943step1 raw8943step0; decide +kernel
      have hl : raw8943step0Labels = labelEmbedding6 ∘ raw8943step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8943step0 raw8943step0Labels raw8943step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5064 node5064Labels := by rfl

def raw8944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8944step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8944step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8944 raw8944Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw8944 raw8944Labels = mixedMoment B raw8944step0 raw8944step0Labels := by
      have hz : ∀ j, raw8944 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8944step0 = (fun i j => raw8944 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8944step0 raw8944; decide +kernel
      have hl : raw8944step0Labels = raw8944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8944 raw8944Labels permutation265 hz
    mixedMoment B raw8944step0 raw8944step0Labels = mixedMoment B raw8944step1 raw8944step1Labels := by
      have ha : raw8944step1 = (fun i j => raw8944step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8944step1 raw8944step0; decide +kernel
      have hl : raw8944step1Labels = raw8944step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8944step0 raw8944step0Labels permutation32 permutation3
    mixedMoment B raw8944step1 raw8944step1Labels = mixedMoment B raw8944step2 raw8944step2Labels := by
      have ha : raw8944step2 = raw8944step1 := by apply Matrix.ext; unfold raw8944step2 raw8944step1; decide +kernel
      have hl : raw8944step1Labels = labelEmbedding6 ∘ raw8944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8944step1 raw8944step1Labels raw8944step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw8945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8945step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8945step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8945 raw8945Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw8945 raw8945Labels = mixedMoment B raw8945step0 raw8945step0Labels := by
      have hz : ∀ j, raw8945 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8945step0 = (fun i j => raw8945 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8945step0 raw8945; decide +kernel
      have hl : raw8945step0Labels = raw8945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8945 raw8945Labels permutation265 hz
    mixedMoment B raw8945step0 raw8945step0Labels = mixedMoment B raw8945step1 raw8945step1Labels := by
      have ha : raw8945step1 = (fun i j => raw8945step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8945step1 raw8945step0; decide +kernel
      have hl : raw8945step1Labels = raw8945step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8945step0 raw8945step0Labels permutation38 permutation3
    mixedMoment B raw8945step1 raw8945step1Labels = mixedMoment B raw8945step2 raw8945step2Labels := by
      have ha : raw8945step2 = raw8945step1 := by apply Matrix.ext; unfold raw8945step2 raw8945step1; decide +kernel
      have hl : raw8945step1Labels = labelEmbedding6 ∘ raw8945step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8945step1 raw8945step1Labels raw8945step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw8946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw8946step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw8946step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8946 raw8946Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw8946 raw8946Labels = mixedMoment B raw8946step0 raw8946step0Labels := by
      have hz : ∀ j, raw8946 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8946step0 = (fun i j => raw8946 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8946step0 raw8946; decide +kernel
      have hl : raw8946step0Labels = raw8946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8946 raw8946Labels permutation265 hz
    mixedMoment B raw8946step0 raw8946step0Labels = mixedMoment B raw8946step1 raw8946step1Labels := by
      have ha : raw8946step1 = (fun i j => raw8946step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8946step1 raw8946step0; decide +kernel
      have hl : raw8946step1Labels = raw8946step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8946step0 raw8946step0Labels permutation44 permutation3
    mixedMoment B raw8946step1 raw8946step1Labels = mixedMoment B raw8946step2 raw8946step2Labels := by
      have ha : raw8946step2 = raw8946step1 := by apply Matrix.ext; unfold raw8946step2 raw8946step1; decide +kernel
      have hl : raw8946step1Labels = labelEmbedding6 ∘ raw8946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8946step1 raw8946step1Labels raw8946step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw8947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8947 raw8947Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw8947 raw8947Labels = mixedMoment B raw8947step0 raw8947step0Labels := by
      have ha : raw8947step0 = (fun i j => raw8947 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8947step0 raw8947; decide +kernel
      have hl : raw8947step0Labels = raw8947Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8947 raw8947Labels permutation152 permutation3
    _ = mixedMoment B node3976 node3976Labels := by rfl

def raw8948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8948 raw8948Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw8948 raw8948Labels = mixedMoment B raw8948step0 raw8948step0Labels := by
      have hz : ∀ j, raw8948 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8948step0 = (fun i j => raw8948 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8948step0 raw8948; decide +kernel
      have hl : raw8948step0Labels = raw8948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8948 raw8948Labels permutation265 hz
    mixedMoment B raw8948step0 raw8948step0Labels = mixedMoment B raw8948step1 raw8948step1Labels := by
      have ha : raw8948step1 = (fun i j => raw8948step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8948step1 raw8948step0; decide +kernel
      have hl : raw8948step1Labels = raw8948step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8948step0 raw8948step0Labels permutation32 permutation3
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw8949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8949 raw8949Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw8949 raw8949Labels = mixedMoment B raw8949step0 raw8949step0Labels := by
      have hz : ∀ j, raw8949 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8949step0 = (fun i j => raw8949 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8949step0 raw8949; decide +kernel
      have hl : raw8949step0Labels = raw8949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8949 raw8949Labels permutation265 hz
    mixedMoment B raw8949step0 raw8949step0Labels = mixedMoment B raw8949step1 raw8949step1Labels := by
      have ha : raw8949step1 = (fun i j => raw8949step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8949step1 raw8949step0; decide +kernel
      have hl : raw8949step1Labels = raw8949step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8949step0 raw8949step0Labels permutation38 permutation3
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw8950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8950 raw8950Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw8950 raw8950Labels = mixedMoment B raw8950step0 raw8950step0Labels := by
      have hz : ∀ j, raw8950 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8950step0 = (fun i j => raw8950 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8950step0 raw8950; decide +kernel
      have hl : raw8950step0Labels = raw8950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8950 raw8950Labels permutation265 hz
    mixedMoment B raw8950step0 raw8950step0Labels = mixedMoment B raw8950step1 raw8950step1Labels := by
      have ha : raw8950step1 = (fun i j => raw8950step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8950step1 raw8950step0; decide +kernel
      have hl : raw8950step1Labels = raw8950step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8950step0 raw8950step0Labels permutation122 permutation6
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw8951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8951 raw8951Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw8951 raw8951Labels = mixedMoment B raw8951step0 raw8951step0Labels := by
      have hz : ∀ j, raw8951 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8951step0 = (fun i j => raw8951 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8951step0 raw8951; decide +kernel
      have hl : raw8951step0Labels = raw8951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8951 raw8951Labels permutation265 hz
    mixedMoment B raw8951step0 raw8951step0Labels = mixedMoment B raw8951step1 raw8951step1Labels := by
      have ha : raw8951step1 = (fun i j => raw8951step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8951step1 raw8951step0; decide +kernel
      have hl : raw8951step1Labels = raw8951step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8951step0 raw8951step0Labels permutation122 permutation6
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw8952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8952 raw8952Labels = mixedMoment B node1018 node1018Labels := by
  calc
    mixedMoment B raw8952 raw8952Labels = mixedMoment B raw8952step0 raw8952step0Labels := by
      have ha : raw8952step0 = (fun i j => raw8952 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8952step0 raw8952; decide +kernel
      have hl : raw8952step0Labels = raw8952Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8952 raw8952Labels permutation184 permutation3
    _ = mixedMoment B node1018 node1018Labels := by rfl

def raw8953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8953 raw8953Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw8953 raw8953Labels = mixedMoment B raw8953step0 raw8953step0Labels := by
      have ha : raw8953step0 = (fun i j => raw8953 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8953step0 raw8953; decide +kernel
      have hl : raw8953step0Labels = raw8953Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8953 raw8953Labels permutation184 permutation3
    _ = mixedMoment B node2567 node2567Labels := by rfl

def raw8954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8954 raw8954Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw8954 raw8954Labels = mixedMoment B raw8954step0 raw8954step0Labels := by
      have ha : raw8954step0 = (fun i j => raw8954 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8954step0 raw8954; decide +kernel
      have hl : raw8954step0Labels = raw8954Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8954 raw8954Labels permutation208 permutation3
    _ = mixedMoment B node2567 node2567Labels := by rfl

def raw8955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8955 raw8955Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw8955 raw8955Labels = mixedMoment B raw8955step0 raw8955step0Labels := by
      have ha : raw8955step0 = (fun i j => raw8955 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8955step0 raw8955; decide +kernel
      have hl : raw8955step0Labels = raw8955Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8955 raw8955Labels permutation232 permutation3
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw8956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8956step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8956 raw8956Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw8956 raw8956Labels = mixedMoment B raw8956step0 raw8956step0Labels := by
      have ha : raw8956step0 = (fun i j => raw8956 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8956step0 raw8956; decide +kernel
      have hl : raw8956step0Labels = raw8956Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8956 raw8956Labels permutation185 permutation3
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw8957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8957 raw8957Labels = mixedMoment B node1036 node1036Labels := by
  calc
    mixedMoment B raw8957 raw8957Labels = mixedMoment B raw8957step0 raw8957step0Labels := by
      have hz : ∀ j, raw8957 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8957step0 = (fun i j => raw8957 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8957step0 raw8957; decide +kernel
      have hl : raw8957step0Labels = raw8957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8957 raw8957Labels permutation265 hz
    mixedMoment B raw8957step0 raw8957step0Labels = mixedMoment B raw8957step1 raw8957step1Labels := by
      have ha : raw8957step1 = (fun i j => raw8957step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8957step1 raw8957step0; decide +kernel
      have hl : raw8957step1Labels = raw8957step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8957step0 raw8957step0Labels permutation40 permutation3
    _ = mixedMoment B node1036 node1036Labels := by rfl

def raw8958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8958 raw8958Labels = mixedMoment B node2478 node2478Labels := by
  calc
    mixedMoment B raw8958 raw8958Labels = mixedMoment B raw8958step0 raw8958step0Labels := by
      have ha : raw8958step0 = (fun i j => raw8958 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8958step0 raw8958; decide +kernel
      have hl : raw8958step0Labels = raw8958Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8958 raw8958Labels permutation160 permutation3
    _ = mixedMoment B node2478 node2478Labels := by rfl

def raw8959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8959 raw8959Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw8959 raw8959Labels = mixedMoment B raw8959step0 raw8959step0Labels := by
      have hz : ∀ j, raw8959 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8959step0 = (fun i j => raw8959 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8959step0 raw8959; decide +kernel
      have hl : raw8959step0Labels = raw8959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8959 raw8959Labels permutation265 hz
    mixedMoment B raw8959step0 raw8959step0Labels = mixedMoment B raw8959step1 raw8959step1Labels := by
      have ha : raw8959step1 = (fun i j => raw8959step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8959step1 raw8959step0; decide +kernel
      have hl : raw8959step1Labels = raw8959step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8959step0 raw8959step0Labels permutation40 permutation3
    _ = mixedMoment B node2591 node2591Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
