import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13824 raw13824Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw13824 raw13824Labels = mixedMoment B raw13824step0 raw13824step0Labels := by
      have ha : raw13824step0 = (fun i j => raw13824 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13824step0 raw13824; decide +kernel
      have hl : raw13824step0Labels = raw13824Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13824 raw13824Labels permutation195 permutation3
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw13825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13825 raw13825Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw13825 raw13825Labels = mixedMoment B raw13825step0 raw13825step0Labels := by
      have ha : raw13825step0 = (fun i j => raw13825 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13825step0 raw13825; decide +kernel
      have hl : raw13825step0Labels = raw13825Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13825 raw13825Labels permutation180 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

def raw13826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13826 raw13826Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw13826 raw13826Labels = mixedMoment B raw13826step0 raw13826step0Labels := by
      have ha : raw13826step0 = (fun i j => raw13826 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13826step0 raw13826; decide +kernel
      have hl : raw13826step0Labels = raw13826Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13826 raw13826Labels permutation156 permutation3
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw13827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13827 raw13827Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw13827 raw13827Labels = mixedMoment B raw13827step0 raw13827step0Labels := by
      have ha : raw13827step0 = (fun i j => raw13827 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13827step0 raw13827; decide +kernel
      have hl : raw13827step0Labels = raw13827Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13827 raw13827Labels permutation180 permutation3
    _ = mixedMoment B node2382 node2382Labels := by rfl

def raw13828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw13828step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13828 raw13828Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw13828 raw13828Labels = mixedMoment B raw13828step0 raw13828step0Labels := by
      have hz : ∀ j, raw13828 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13828step0 = (fun i j => raw13828 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13828step0 raw13828; decide +kernel
      have hl : raw13828step0Labels = raw13828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13828 raw13828Labels permutation434 hz
    mixedMoment B raw13828step0 raw13828step0Labels = mixedMoment B raw13828step1 raw13828step1Labels := by
      have ha : raw13828step1 = (fun i j => raw13828step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13828step1 raw13828step0; decide +kernel
      have hl : raw13828step1Labels = raw13828step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13828step0 raw13828step0Labels permutation39 permutation3
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw13829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw13829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13829 raw13829Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw13829 raw13829Labels = mixedMoment B raw13829step0 raw13829step0Labels := by
      have ha : raw13829step0 = (fun i j => raw13829 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13829step0 raw13829; decide +kernel
      have hl : raw13829step0Labels = raw13829Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13829 raw13829Labels permutation194 permutation3
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw13830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13830 raw13830Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw13830 raw13830Labels = mixedMoment B raw13830step0 raw13830step0Labels := by
      have ha : raw13830step0 = (fun i j => raw13830 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13830step0 raw13830; decide +kernel
      have hl : raw13830step0Labels = raw13830Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13830 raw13830Labels permutation176 permutation3
    _ = mixedMoment B node980 node980Labels := by rfl

def raw13831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13831 raw13831Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw13831 raw13831Labels = mixedMoment B raw13831step0 raw13831step0Labels := by
      have ha : raw13831step0 = (fun i j => raw13831 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13831step0 raw13831; decide +kernel
      have hl : raw13831step0Labels = raw13831Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13831 raw13831Labels permutation152 permutation3
    _ = mixedMoment B node2556 node2556Labels := by rfl

def raw13832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13832 raw13832Labels = mixedMoment B node2383 node2383Labels := by
  calc
    mixedMoment B raw13832 raw13832Labels = mixedMoment B raw13832step0 raw13832step0Labels := by
      have ha : raw13832step0 = (fun i j => raw13832 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13832step0 raw13832; decide +kernel
      have hl : raw13832step0Labels = raw13832Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13832 raw13832Labels permutation176 permutation3
    _ = mixedMoment B node2383 node2383Labels := by rfl

def raw13833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13833step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13833 raw13833Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw13833 raw13833Labels = mixedMoment B raw13833step0 raw13833step0Labels := by
      have hz : ∀ j, raw13833 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13833step0 = (fun i j => raw13833 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13833step0 raw13833; decide +kernel
      have hl : raw13833step0Labels = raw13833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13833 raw13833Labels permutation434 hz
    mixedMoment B raw13833step0 raw13833step0Labels = mixedMoment B raw13833step1 raw13833step1Labels := by
      have ha : raw13833step1 = (fun i j => raw13833step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13833step1 raw13833step0; decide +kernel
      have hl : raw13833step1Labels = raw13833step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13833step0 raw13833step0Labels permutation38 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw13834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw13834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13834 raw13834Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw13834 raw13834Labels = mixedMoment B raw13834step0 raw13834step0Labels := by
      have hz : ∀ j, raw13834 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13834step0 = (fun i j => raw13834 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13834step0 raw13834; decide +kernel
      have hl : raw13834step0Labels = raw13834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13834 raw13834Labels permutation520 hz
    mixedMoment B raw13834step0 raw13834step0Labels = mixedMoment B raw13834step1 raw13834step1Labels := by
      have ha : raw13834step1 = (fun i j => raw13834step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13834step1 raw13834step0; decide +kernel
      have hl : raw13834step1Labels = raw13834step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13834step0 raw13834step0Labels permutation38 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw13835 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13835step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13835step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13835 raw13835Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13835 raw13835Labels = mixedMoment B raw13835step0 raw13835step0Labels := by
      have hz : ∀ j, raw13835 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13835step0 = (fun i j => raw13835 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13835step0 raw13835; decide +kernel
      have hl : raw13835step0Labels = raw13835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13835 raw13835Labels permutation265 hz
    mixedMoment B raw13835step0 raw13835step0Labels = mixedMoment B raw13835step1 raw13835step1Labels := by
      have ha : raw13835step1 = (fun i j => raw13835step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13835step1 raw13835step0; decide +kernel
      have hl : raw13835step1Labels = raw13835step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13835step0 raw13835step0Labels permutation32 permutation7
    mixedMoment B raw13835step1 raw13835step1Labels = mixedMoment B raw13835step2 raw13835step2Labels := by
      have ha : raw13835step2 = raw13835step1 := by apply Matrix.ext; unfold raw13835step2 raw13835step1; decide +kernel
      have hl : raw13835step1Labels = labelEmbedding10 ∘ raw13835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13835step1 raw13835step1Labels raw13835step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw13836 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13836step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13836 raw13836Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13836 raw13836Labels = mixedMoment B raw13836step0 raw13836step0Labels := by
      have ha : raw13836step0 = (fun i j => raw13836 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13836step0 raw13836; decide +kernel
      have hl : raw13836step0Labels = raw13836Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13836 raw13836Labels permutation152 permutation7
    mixedMoment B raw13836step0 raw13836step0Labels = mixedMoment B raw13836step1 raw13836step1Labels := by
      have ha : raw13836step1 = raw13836step0 := by apply Matrix.ext; unfold raw13836step1 raw13836step0; decide +kernel
      have hl : raw13836step0Labels = labelEmbedding10 ∘ raw13836step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13836step0 raw13836step0Labels raw13836step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw13837 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13837step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13837 raw13837Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13837 raw13837Labels = mixedMoment B raw13837step0 raw13837step0Labels := by
      have ha : raw13837step0 = (fun i j => raw13837 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13837step0 raw13837; decide +kernel
      have hl : raw13837step0Labels = raw13837Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13837 raw13837Labels permutation154 permutation7
    mixedMoment B raw13837step0 raw13837step0Labels = mixedMoment B raw13837step1 raw13837step1Labels := by
      have ha : raw13837step1 = raw13837step0 := by apply Matrix.ext; unfold raw13837step1 raw13837step0; decide +kernel
      have hl : raw13837step0Labels = labelEmbedding10 ∘ raw13837step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13837step0 raw13837step0Labels raw13837step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw13838 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13838step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13838 raw13838Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13838 raw13838Labels = mixedMoment B raw13838step0 raw13838step0Labels := by
      have ha : raw13838step0 = (fun i j => raw13838 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13838step0 raw13838; decide +kernel
      have hl : raw13838step0Labels = raw13838Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13838 raw13838Labels permutation152 permutation7
    mixedMoment B raw13838step0 raw13838step0Labels = mixedMoment B raw13838step1 raw13838step1Labels := by
      have ha : raw13838step1 = raw13838step0 := by apply Matrix.ext; unfold raw13838step1 raw13838step0; decide +kernel
      have hl : raw13838step0Labels = labelEmbedding10 ∘ raw13838step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13838step0 raw13838step0Labels raw13838step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw13839 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13839step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13839step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13839step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13839step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13839 raw13839Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw13839 raw13839Labels = mixedMoment B raw13839step0 raw13839step0Labels := by
      have ha : raw13839step0 = (fun i j => raw13839 (permutation197 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13839step0 raw13839; decide +kernel
      have hl : raw13839step0Labels = raw13839Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13839 raw13839Labels permutation197 permutation4
    mixedMoment B raw13839step0 raw13839step0Labels = mixedMoment B raw13839step1 raw13839step1Labels := by
      have ha : raw13839step1 = -raw13839step0 := by apply Matrix.ext; change ∀ i j, raw13839step1 i j = -(raw13839step0 i j); unfold raw13839step1 raw13839step0; decide +kernel
      have hl : raw13839step1Labels = raw13839step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13839step1 raw13839step1Labels = mixedMoment B raw13839step2 raw13839step2Labels := by
      have ha : raw13839step2 = raw13839step1 := by apply Matrix.ext; unfold raw13839step2 raw13839step1; decide +kernel
      have hl : raw13839step1Labels = labelEmbedding7 ∘ raw13839step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13839step1 raw13839step1Labels raw13839step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw13840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13840step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13840step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13840step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13840 raw13840Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw13840 raw13840Labels = mixedMoment B raw13840step0 raw13840step0Labels := by
      have ha : raw13840step0 = (fun i j => raw13840 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13840step0 raw13840; decide +kernel
      have hl : raw13840step0Labels = raw13840Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13840 raw13840Labels permutation180 permutation6
    mixedMoment B raw13840step0 raw13840step0Labels = mixedMoment B raw13840step1 raw13840step1Labels := by
      have ha : raw13840step1 = raw13840step0 := by apply Matrix.ext; unfold raw13840step1 raw13840step0; decide +kernel
      have hl : raw13840step0Labels = labelEmbedding9 ∘ raw13840step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13840step0 raw13840step0Labels raw13840step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw13841 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13841step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13841 raw13841Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13841 raw13841Labels = mixedMoment B raw13841step0 raw13841step0Labels := by
      have ha : raw13841step0 = (fun i j => raw13841 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13841step0 raw13841; decide +kernel
      have hl : raw13841step0Labels = raw13841Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13841 raw13841Labels permutation177 permutation6
    mixedMoment B raw13841step0 raw13841step0Labels = mixedMoment B raw13841step1 raw13841step1Labels := by
      have ha : raw13841step1 = raw13841step0 := by apply Matrix.ext; unfold raw13841step1 raw13841step0; decide +kernel
      have hl : raw13841step0Labels = labelEmbedding9 ∘ raw13841step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13841step0 raw13841step0Labels raw13841step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw13842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13842step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13842step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13842 raw13842Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13842 raw13842Labels = mixedMoment B raw13842step0 raw13842step0Labels := by
      have ha : raw13842step0 = (fun i j => raw13842 (permutation179 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13842step0 raw13842; decide +kernel
      have hl : raw13842step0Labels = raw13842Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13842 raw13842Labels permutation179 permutation6
    mixedMoment B raw13842step0 raw13842step0Labels = mixedMoment B raw13842step1 raw13842step1Labels := by
      have ha : raw13842step1 = raw13842step0 := by apply Matrix.ext; unfold raw13842step1 raw13842step0; decide +kernel
      have hl : raw13842step0Labels = labelEmbedding9 ∘ raw13842step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13842step0 raw13842step0Labels raw13842step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw13843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13843step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13843 raw13843Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw13843 raw13843Labels = mixedMoment B raw13843step0 raw13843step0Labels := by
      have hz : ∀ j, raw13843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13843step0 = (fun i j => raw13843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13843step0 raw13843; decide +kernel
      have hl : raw13843step0Labels = raw13843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13843 raw13843Labels permutation346 hz
    mixedMoment B raw13843step0 raw13843step0Labels = mixedMoment B raw13843step1 raw13843step1Labels := by
      have ha : raw13843step1 = (fun i j => raw13843step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13843step1 raw13843step0; decide +kernel
      have hl : raw13843step1Labels = raw13843step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13843step0 raw13843step0Labels permutation36 permutation6
    mixedMoment B raw13843step1 raw13843step1Labels = mixedMoment B raw13843step2 raw13843step2Labels := by
      have ha : raw13843step2 = raw13843step1 := by apply Matrix.ext; unfold raw13843step2 raw13843step1; decide +kernel
      have hl : raw13843step1Labels = labelEmbedding9 ∘ raw13843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13843step1 raw13843step1Labels raw13843step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw13844 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13844step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13844step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13844step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13844step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13844 raw13844Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw13844 raw13844Labels = mixedMoment B raw13844step0 raw13844step0Labels := by
      have ha : raw13844step0 = (fun i j => raw13844 (permutation195 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13844step0 raw13844; decide +kernel
      have hl : raw13844step0Labels = raw13844Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13844 raw13844Labels permutation195 permutation4
    mixedMoment B raw13844step0 raw13844step0Labels = mixedMoment B raw13844step1 raw13844step1Labels := by
      have ha : raw13844step1 = -raw13844step0 := by apply Matrix.ext; change ∀ i j, raw13844step1 i j = -(raw13844step0 i j); unfold raw13844step1 raw13844step0; decide +kernel
      have hl : raw13844step1Labels = raw13844step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13844step1 raw13844step1Labels = mixedMoment B raw13844step2 raw13844step2Labels := by
      have ha : raw13844step2 = raw13844step1 := by apply Matrix.ext; unfold raw13844step2 raw13844step1; decide +kernel
      have hl : raw13844step1Labels = labelEmbedding7 ∘ raw13844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13844step1 raw13844step1Labels raw13844step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw13845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13845step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13845 raw13845Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw13845 raw13845Labels = mixedMoment B raw13845step0 raw13845step0Labels := by
      have hz : ∀ j, raw13845 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13845step0 = (fun i j => raw13845 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13845step0 raw13845; decide +kernel
      have hl : raw13845step0Labels = raw13845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13845 raw13845Labels permutation265 hz
    mixedMoment B raw13845step0 raw13845step0Labels = mixedMoment B raw13845step1 raw13845step1Labels := by
      have ha : raw13845step1 = (fun i j => raw13845step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13845step1 raw13845step0; decide +kernel
      have hl : raw13845step1Labels = raw13845step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13845step0 raw13845step0Labels permutation37 permutation6
    mixedMoment B raw13845step1 raw13845step1Labels = mixedMoment B raw13845step2 raw13845step2Labels := by
      have ha : raw13845step2 = raw13845step1 := by apply Matrix.ext; unfold raw13845step2 raw13845step1; decide +kernel
      have hl : raw13845step1Labels = labelEmbedding9 ∘ raw13845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13845step1 raw13845step1Labels raw13845step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw13846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13846step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13846 raw13846Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw13846 raw13846Labels = mixedMoment B raw13846step0 raw13846step0Labels := by
      have ha : raw13846step0 = (fun i j => raw13846 (permutation181 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13846step0 raw13846; decide +kernel
      have hl : raw13846step0Labels = raw13846Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13846 raw13846Labels permutation181 permutation6
    mixedMoment B raw13846step0 raw13846step0Labels = mixedMoment B raw13846step1 raw13846step1Labels := by
      have ha : raw13846step1 = raw13846step0 := by apply Matrix.ext; unfold raw13846step1 raw13846step0; decide +kernel
      have hl : raw13846step0Labels = labelEmbedding9 ∘ raw13846step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13846step0 raw13846step0Labels raw13846step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw13847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13847step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13847 raw13847Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw13847 raw13847Labels = mixedMoment B raw13847step0 raw13847step0Labels := by
      have ha : raw13847step0 = (fun i j => raw13847 (permutation179 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13847step0 raw13847; decide +kernel
      have hl : raw13847step0Labels = raw13847Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13847 raw13847Labels permutation179 permutation6
    mixedMoment B raw13847step0 raw13847step0Labels = mixedMoment B raw13847step1 raw13847step1Labels := by
      have ha : raw13847step1 = raw13847step0 := by apply Matrix.ext; unfold raw13847step1 raw13847step0; decide +kernel
      have hl : raw13847step0Labels = labelEmbedding9 ∘ raw13847step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13847step0 raw13847step0Labels raw13847step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw13848 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13848step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13848step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13848step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13848 raw13848Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw13848 raw13848Labels = mixedMoment B raw13848step0 raw13848step0Labels := by
      have ha : raw13848step0 = (fun i j => raw13848 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13848step0 raw13848; decide +kernel
      have hl : raw13848step0Labels = raw13848Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13848 raw13848Labels permutation194 permutation4
    mixedMoment B raw13848step0 raw13848step0Labels = mixedMoment B raw13848step1 raw13848step1Labels := by
      have ha : raw13848step1 = -raw13848step0 := by apply Matrix.ext; change ∀ i j, raw13848step1 i j = -(raw13848step0 i j); unfold raw13848step1 raw13848step0; decide +kernel
      have hl : raw13848step1Labels = raw13848step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13848step1 raw13848step1Labels = mixedMoment B raw13848step2 raw13848step2Labels := by
      have ha : raw13848step2 = raw13848step1 := by apply Matrix.ext; unfold raw13848step2 raw13848step1; decide +kernel
      have hl : raw13848step1Labels = labelEmbedding7 ∘ raw13848step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13848step1 raw13848step1Labels raw13848step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw13849 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13849step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13849 raw13849Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw13849 raw13849Labels = mixedMoment B raw13849step0 raw13849step0Labels := by
      have hz : ∀ j, raw13849 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13849step0 = (fun i j => raw13849 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13849step0 raw13849; decide +kernel
      have hl : raw13849step0Labels = raw13849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13849 raw13849Labels permutation265 hz
    mixedMoment B raw13849step0 raw13849step0Labels = mixedMoment B raw13849step1 raw13849step1Labels := by
      have ha : raw13849step1 = (fun i j => raw13849step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13849step1 raw13849step0; decide +kernel
      have hl : raw13849step1Labels = raw13849step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13849step0 raw13849step0Labels permutation36 permutation6
    mixedMoment B raw13849step1 raw13849step1Labels = mixedMoment B raw13849step2 raw13849step2Labels := by
      have ha : raw13849step2 = raw13849step1 := by apply Matrix.ext; unfold raw13849step2 raw13849step1; decide +kernel
      have hl : raw13849step1Labels = labelEmbedding9 ∘ raw13849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13849step1 raw13849step1Labels raw13849step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw13850 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13850step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13850 raw13850Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw13850 raw13850Labels = mixedMoment B raw13850step0 raw13850step0Labels := by
      have ha : raw13850step0 = (fun i j => raw13850 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13850step0 raw13850; decide +kernel
      have hl : raw13850step0Labels = raw13850Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13850 raw13850Labels permutation180 permutation6
    mixedMoment B raw13850step0 raw13850step0Labels = mixedMoment B raw13850step1 raw13850step1Labels := by
      have ha : raw13850step1 = raw13850step0 := by apply Matrix.ext; unfold raw13850step1 raw13850step0; decide +kernel
      have hl : raw13850step0Labels = labelEmbedding9 ∘ raw13850step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13850step0 raw13850step0Labels raw13850step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw13851 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13851step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13851 raw13851Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw13851 raw13851Labels = mixedMoment B raw13851step0 raw13851step0Labels := by
      have ha : raw13851step0 = (fun i j => raw13851 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13851step0 raw13851; decide +kernel
      have hl : raw13851step0Labels = raw13851Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13851 raw13851Labels permutation177 permutation6
    mixedMoment B raw13851step0 raw13851step0Labels = mixedMoment B raw13851step1 raw13851step1Labels := by
      have ha : raw13851step1 = raw13851step0 := by apply Matrix.ext; unfold raw13851step1 raw13851step0; decide +kernel
      have hl : raw13851step0Labels = labelEmbedding9 ∘ raw13851step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13851step0 raw13851step0Labels raw13851step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw13852 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13852step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13852step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13852step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13852 raw13852Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw13852 raw13852Labels = mixedMoment B raw13852step0 raw13852step0Labels := by
      have ha : raw13852step0 = (fun i j => raw13852 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13852step0 raw13852; decide +kernel
      have hl : raw13852step0Labels = raw13852Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13852 raw13852Labels permutation176 permutation4
    mixedMoment B raw13852step0 raw13852step0Labels = mixedMoment B raw13852step1 raw13852step1Labels := by
      have ha : raw13852step1 = -raw13852step0 := by apply Matrix.ext; change ∀ i j, raw13852step1 i j = -(raw13852step0 i j); unfold raw13852step1 raw13852step0; decide +kernel
      have hl : raw13852step1Labels = raw13852step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13852step1 raw13852step1Labels = mixedMoment B raw13852step2 raw13852step2Labels := by
      have ha : raw13852step2 = raw13852step1 := by apply Matrix.ext; unfold raw13852step2 raw13852step1; decide +kernel
      have hl : raw13852step1Labels = labelEmbedding7 ∘ raw13852step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13852step1 raw13852step1Labels raw13852step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

def raw13853 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13853step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13853step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13853 raw13853Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw13853 raw13853Labels = mixedMoment B raw13853step0 raw13853step0Labels := by
      have hz : ∀ j, raw13853 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13853step0 = (fun i j => raw13853 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13853step0 raw13853; decide +kernel
      have hl : raw13853step0Labels = raw13853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13853 raw13853Labels permutation265 hz
    mixedMoment B raw13853step0 raw13853step0Labels = mixedMoment B raw13853step1 raw13853step1Labels := by
      have ha : raw13853step1 = (fun i j => raw13853step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13853step1 raw13853step0; decide +kernel
      have hl : raw13853step1Labels = raw13853step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13853step0 raw13853step0Labels permutation32 permutation6
    mixedMoment B raw13853step1 raw13853step1Labels = mixedMoment B raw13853step2 raw13853step2Labels := by
      have ha : raw13853step2 = raw13853step1 := by apply Matrix.ext; unfold raw13853step2 raw13853step1; decide +kernel
      have hl : raw13853step1Labels = labelEmbedding9 ∘ raw13853step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13853step1 raw13853step1Labels raw13853step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw13854 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13854step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13854 raw13854Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw13854 raw13854Labels = mixedMoment B raw13854step0 raw13854step0Labels := by
      have ha : raw13854step0 = (fun i j => raw13854 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13854step0 raw13854; decide +kernel
      have hl : raw13854step0Labels = raw13854Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13854 raw13854Labels permutation176 permutation6
    mixedMoment B raw13854step0 raw13854step0Labels = mixedMoment B raw13854step1 raw13854step1Labels := by
      have ha : raw13854step1 = raw13854step0 := by apply Matrix.ext; unfold raw13854step1 raw13854step0; decide +kernel
      have hl : raw13854step0Labels = labelEmbedding9 ∘ raw13854step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13854step0 raw13854step0Labels raw13854step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

def raw13855 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13855step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13855 raw13855Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13855 raw13855Labels = mixedMoment B raw13855step0 raw13855step0Labels := by
      have ha : raw13855step0 = (fun i j => raw13855 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13855step0 raw13855; decide +kernel
      have hl : raw13855step0Labels = raw13855Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13855 raw13855Labels permutation176 permutation6
    mixedMoment B raw13855step0 raw13855step0Labels = mixedMoment B raw13855step1 raw13855step1Labels := by
      have ha : raw13855step1 = raw13855step0 := by apply Matrix.ext; unfold raw13855step1 raw13855step0; decide +kernel
      have hl : raw13855step0Labels = labelEmbedding9 ∘ raw13855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13855step0 raw13855step0Labels raw13855step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw13856 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13856step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13856step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13856 raw13856Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13856 raw13856Labels = mixedMoment B raw13856step0 raw13856step0Labels := by
      have ha : raw13856step0 = (fun i j => raw13856 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13856step0 raw13856; decide +kernel
      have hl : raw13856step0Labels = raw13856Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13856 raw13856Labels permutation178 permutation6
    mixedMoment B raw13856step0 raw13856step0Labels = mixedMoment B raw13856step1 raw13856step1Labels := by
      have ha : raw13856step1 = raw13856step0 := by apply Matrix.ext; unfold raw13856step1 raw13856step0; decide +kernel
      have hl : raw13856step0Labels = labelEmbedding9 ∘ raw13856step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13856step0 raw13856step0Labels raw13856step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw13857 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13857step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13857 raw13857Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13857 raw13857Labels = mixedMoment B raw13857step0 raw13857step0Labels := by
      have hz : ∀ j, raw13857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13857step0 = (fun i j => raw13857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13857step0 raw13857; decide +kernel
      have hl : raw13857step0Labels = raw13857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13857 raw13857Labels permutation265 hz
    mixedMoment B raw13857step0 raw13857step0Labels = mixedMoment B raw13857step1 raw13857step1Labels := by
      have ha : raw13857step1 = (fun i j => raw13857step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13857step1 raw13857step0; decide +kernel
      have hl : raw13857step1Labels = raw13857step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13857step0 raw13857step0Labels permutation36 permutation6
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw13858 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13858 raw13858Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw13858 raw13858Labels = mixedMoment B raw13858step0 raw13858step0Labels := by
      have ha : raw13858step0 = (fun i j => raw13858 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13858step0 raw13858; decide +kernel
      have hl : raw13858step0Labels = raw13858Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13858 raw13858Labels permutation180 permutation6
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw13859 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13859 raw13859Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw13859 raw13859Labels = mixedMoment B raw13859step0 raw13859step0Labels := by
      have ha : raw13859step0 = (fun i j => raw13859 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13859step0 raw13859; decide +kernel
      have hl : raw13859step0Labels = raw13859Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13859 raw13859Labels permutation177 permutation6
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw13860 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13860 raw13860Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw13860 raw13860Labels = mixedMoment B raw13860step0 raw13860step0Labels := by
      have ha : raw13860step0 = (fun i j => raw13860 (permutation179 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13860step0 raw13860; decide +kernel
      have hl : raw13860step0Labels = raw13860Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13860 raw13860Labels permutation179 permutation6
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw13861 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13861 raw13861Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw13861 raw13861Labels = mixedMoment B raw13861step0 raw13861step0Labels := by
      have ha : raw13861step0 = (fun i j => raw13861 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13861step0 raw13861; decide +kernel
      have hl : raw13861step0Labels = raw13861Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13861 raw13861Labels permutation180 permutation6
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw13862 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13862 raw13862Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw13862 raw13862Labels = mixedMoment B raw13862step0 raw13862step0Labels := by
      have ha : raw13862step0 = (fun i j => raw13862 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13862step0 raw13862; decide +kernel
      have hl : raw13862step0Labels = raw13862Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13862 raw13862Labels permutation180 permutation6
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw13863 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13863Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13863 raw13863Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw13863 raw13863Labels = mixedMoment B raw13863step0 raw13863step0Labels := by
      have ha : raw13863step0 = (fun i j => raw13863 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13863step0 raw13863; decide +kernel
      have hl : raw13863step0Labels = raw13863Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13863 raw13863Labels permutation177 permutation6
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw13864 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13864 raw13864Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw13864 raw13864Labels = mixedMoment B raw13864step0 raw13864step0Labels := by
      have ha : raw13864step0 = (fun i j => raw13864 (permutation179 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13864step0 raw13864; decide +kernel
      have hl : raw13864step0Labels = raw13864Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13864 raw13864Labels permutation179 permutation6
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw13865 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13865step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13865 raw13865Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13865 raw13865Labels = mixedMoment B raw13865step0 raw13865step0Labels := by
      have hz : ∀ j, raw13865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13865step0 = (fun i j => raw13865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13865step0 raw13865; decide +kernel
      have hl : raw13865step0Labels = raw13865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13865 raw13865Labels permutation346 hz
    mixedMoment B raw13865step0 raw13865step0Labels = mixedMoment B raw13865step1 raw13865step1Labels := by
      have ha : raw13865step1 = (fun i j => raw13865step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13865step1 raw13865step0; decide +kernel
      have hl : raw13865step1Labels = raw13865step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13865step0 raw13865step0Labels permutation36 permutation6
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw13866 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13866 raw13866Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw13866 raw13866Labels = mixedMoment B raw13866step0 raw13866step0Labels := by
      have ha : raw13866step0 = (fun i j => raw13866 (permutation181 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13866step0 raw13866; decide +kernel
      have hl : raw13866step0Labels = raw13866Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13866 raw13866Labels permutation181 permutation6
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw13867 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13867 raw13867Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw13867 raw13867Labels = mixedMoment B raw13867step0 raw13867step0Labels := by
      have hz : ∀ j, raw13867 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13867step0 = (fun i j => raw13867 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13867step0 raw13867; decide +kernel
      have hl : raw13867step0Labels = raw13867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13867 raw13867Labels permutation265 hz
    mixedMoment B raw13867step0 raw13867step0Labels = mixedMoment B raw13867step1 raw13867step1Labels := by
      have ha : raw13867step1 = (fun i j => raw13867step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13867step1 raw13867step0; decide +kernel
      have hl : raw13867step1Labels = raw13867step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13867step0 raw13867step0Labels permutation37 permutation6
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw13868 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13868 raw13868Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw13868 raw13868Labels = mixedMoment B raw13868step0 raw13868step0Labels := by
      have ha : raw13868step0 = (fun i j => raw13868 (permutation181 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13868step0 raw13868; decide +kernel
      have hl : raw13868step0Labels = raw13868Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13868 raw13868Labels permutation181 permutation6
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw13869 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13869 raw13869Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw13869 raw13869Labels = mixedMoment B raw13869step0 raw13869step0Labels := by
      have ha : raw13869step0 = (fun i j => raw13869 (permutation179 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13869step0 raw13869; decide +kernel
      have hl : raw13869step0Labels = raw13869Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13869 raw13869Labels permutation179 permutation6
    _ = mixedMoment B node2720 node2720Labels := by rfl

def raw13870 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13870 raw13870Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw13870 raw13870Labels = mixedMoment B raw13870step0 raw13870step0Labels := by
      have ha : raw13870step0 = (fun i j => raw13870 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13870step0 raw13870; decide +kernel
      have hl : raw13870step0Labels = raw13870Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13870 raw13870Labels permutation180 permutation6
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw13871 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13871step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13871 raw13871Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw13871 raw13871Labels = mixedMoment B raw13871step0 raw13871step0Labels := by
      have hz : ∀ j, raw13871 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13871step0 = (fun i j => raw13871 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13871step0 raw13871; decide +kernel
      have hl : raw13871step0Labels = raw13871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13871 raw13871Labels permutation265 hz
    mixedMoment B raw13871step0 raw13871step0Labels = mixedMoment B raw13871step1 raw13871step1Labels := by
      have ha : raw13871step1 = (fun i j => raw13871step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13871step1 raw13871step0; decide +kernel
      have hl : raw13871step1Labels = raw13871step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13871step0 raw13871step0Labels permutation36 permutation6
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw13872 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13872 raw13872Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw13872 raw13872Labels = mixedMoment B raw13872step0 raw13872step0Labels := by
      have ha : raw13872step0 = (fun i j => raw13872 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13872step0 raw13872; decide +kernel
      have hl : raw13872step0Labels = raw13872Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13872 raw13872Labels permutation180 permutation6
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw13873 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13873 raw13873Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw13873 raw13873Labels = mixedMoment B raw13873step0 raw13873step0Labels := by
      have ha : raw13873step0 = (fun i j => raw13873 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13873step0 raw13873; decide +kernel
      have hl : raw13873step0Labels = raw13873Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13873 raw13873Labels permutation177 permutation6
    _ = mixedMoment B node2720 node2720Labels := by rfl

def raw13874 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13874 raw13874Labels = mixedMoment B node2204 node2204Labels := by
  calc
    mixedMoment B raw13874 raw13874Labels = mixedMoment B raw13874step0 raw13874step0Labels := by
      have ha : raw13874step0 = (fun i j => raw13874 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13874step0 raw13874; decide +kernel
      have hl : raw13874step0Labels = raw13874Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13874 raw13874Labels permutation176 permutation6
    _ = mixedMoment B node2204 node2204Labels := by rfl

def raw13875 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13875step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13875 raw13875Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw13875 raw13875Labels = mixedMoment B raw13875step0 raw13875step0Labels := by
      have hz : ∀ j, raw13875 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13875step0 = (fun i j => raw13875 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13875step0 raw13875; decide +kernel
      have hl : raw13875step0Labels = raw13875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13875 raw13875Labels permutation265 hz
    mixedMoment B raw13875step0 raw13875step0Labels = mixedMoment B raw13875step1 raw13875step1Labels := by
      have ha : raw13875step1 = (fun i j => raw13875step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13875step1 raw13875step0; decide +kernel
      have hl : raw13875step1Labels = raw13875step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13875step0 raw13875step0Labels permutation32 permutation6
    _ = mixedMoment B node2741 node2741Labels := by rfl

def raw13876 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13876 raw13876Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw13876 raw13876Labels = mixedMoment B raw13876step0 raw13876step0Labels := by
      have ha : raw13876step0 = (fun i j => raw13876 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13876step0 raw13876; decide +kernel
      have hl : raw13876step0Labels = raw13876Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13876 raw13876Labels permutation176 permutation6
    _ = mixedMoment B node2671 node2671Labels := by rfl

def raw13877 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13877 raw13877Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13877 raw13877Labels = mixedMoment B raw13877step0 raw13877step0Labels := by
      have ha : raw13877step0 = (fun i j => raw13877 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13877step0 raw13877; decide +kernel
      have hl : raw13877step0Labels = raw13877Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13877 raw13877Labels permutation176 permutation6
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw13878 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13878 raw13878Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13878 raw13878Labels = mixedMoment B raw13878step0 raw13878step0Labels := by
      have ha : raw13878step0 = (fun i j => raw13878 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13878step0 raw13878; decide +kernel
      have hl : raw13878step0Labels = raw13878Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13878 raw13878Labels permutation178 permutation6
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw13879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13879 raw13879Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw13879 raw13879Labels = mixedMoment B raw13879step0 raw13879step0Labels := by
      have hz : ∀ j, raw13879 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13879step0 = (fun i j => raw13879 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13879step0 raw13879; decide +kernel
      have hl : raw13879step0Labels = raw13879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13879 raw13879Labels permutation346 hz
    mixedMoment B raw13879step0 raw13879step0Labels = mixedMoment B raw13879step1 raw13879step1Labels := by
      have ha : raw13879step1 = (fun i j => raw13879step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13879step1 raw13879step0; decide +kernel
      have hl : raw13879step1Labels = raw13879step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13879step0 raw13879step0Labels permutation37 permutation2
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw13880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13880 raw13880Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw13880 raw13880Labels = mixedMoment B raw13880step0 raw13880step0Labels := by
      have hz : ∀ j, raw13880 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13880step0 = (fun i j => raw13880 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13880step0 raw13880; decide +kernel
      have hl : raw13880step0Labels = raw13880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13880 raw13880Labels permutation265 hz
    mixedMoment B raw13880step0 raw13880step0Labels = mixedMoment B raw13880step1 raw13880step1Labels := by
      have ha : raw13880step1 = (fun i j => raw13880step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13880step1 raw13880step0; decide +kernel
      have hl : raw13880step1Labels = raw13880step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13880step0 raw13880step0Labels permutation37 permutation2
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw13881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw13881step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13881step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw13881step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13881 raw13881Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw13881 raw13881Labels = mixedMoment B raw13881step0 raw13881step0Labels := by
      have hz : ∀ j, raw13881 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13881step0 = (fun i j => raw13881 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13881step0 raw13881; decide +kernel
      have hl : raw13881step0Labels = raw13881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13881 raw13881Labels permutation346 hz
    mixedMoment B raw13881step0 raw13881step0Labels = mixedMoment B raw13881step1 raw13881step1Labels := by
      have hz : ∀ j, raw13881step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13881step1 = (fun i j => raw13881step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13881step1 raw13881step0; decide +kernel
      have hl : raw13881step1Labels = raw13881step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13881step0 raw13881step0Labels permutation56 hz
    mixedMoment B raw13881step1 raw13881step1Labels = mixedMoment B raw13881step2 raw13881step2Labels := by
      have ha : raw13881step2 = (fun i j => raw13881step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13881step2 raw13881step1; decide +kernel
      have hl : raw13881step2Labels = raw13881step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13881step1 raw13881step1Labels permutation17 permutation6
    mixedMoment B raw13881step2 raw13881step2Labels = mixedMoment B raw13881step3 raw13881step3Labels := by
      have ha : raw13881step3 = raw13881step2 := by apply Matrix.ext; unfold raw13881step3 raw13881step2; decide +kernel
      have hl : raw13881step2Labels = labelEmbedding9 ∘ raw13881step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13881step2 raw13881step2Labels raw13881step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw13882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13882step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13882step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13882step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13882step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13882step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13882 raw13882Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw13882 raw13882Labels = mixedMoment B raw13882step0 raw13882step0Labels := by
      have hz : ∀ j, raw13882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13882step0 = (fun i j => raw13882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13882step0 raw13882; decide +kernel
      have hl : raw13882step0Labels = raw13882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13882 raw13882Labels permutation346 hz
    mixedMoment B raw13882step0 raw13882step0Labels = mixedMoment B raw13882step1 raw13882step1Labels := by
      have hz : ∀ j, raw13882step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13882step1 = (fun i j => raw13882step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13882step1 raw13882step0; decide +kernel
      have hl : raw13882step1Labels = raw13882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13882step0 raw13882step0Labels permutation56 hz
    mixedMoment B raw13882step1 raw13882step1Labels = mixedMoment B raw13882step2 raw13882step2Labels := by
      have ha : raw13882step2 = (fun i j => raw13882step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13882step2 raw13882step1; decide +kernel
      have hl : raw13882step2Labels = raw13882step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13882step1 raw13882step1Labels permutation13 permutation7
    mixedMoment B raw13882step2 raw13882step2Labels = mixedMoment B raw13882step3 raw13882step3Labels := by
      have ha : raw13882step3 = -raw13882step2 := by apply Matrix.ext; change ∀ i j, raw13882step3 i j = -(raw13882step2 i j); unfold raw13882step3 raw13882step2; decide +kernel
      have hl : raw13882step3Labels = raw13882step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13882step3 raw13882step3Labels = mixedMoment B raw13882step4 raw13882step4Labels := by
      have ha : raw13882step4 = raw13882step3 := by apply Matrix.ext; unfold raw13882step4 raw13882step3; decide +kernel
      have hl : raw13882step3Labels = labelEmbedding10 ∘ raw13882step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13882step3 raw13882step3Labels raw13882step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw13883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13883step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13883step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13883step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13883step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13883step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13883step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13883 raw13883Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw13883 raw13883Labels = mixedMoment B raw13883step0 raw13883step0Labels := by
      have hz : ∀ j, raw13883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13883step0 = (fun i j => raw13883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13883step0 raw13883; decide +kernel
      have hl : raw13883step0Labels = raw13883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13883 raw13883Labels permutation346 hz
    mixedMoment B raw13883step0 raw13883step0Labels = mixedMoment B raw13883step1 raw13883step1Labels := by
      have hz : ∀ j, raw13883step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13883step1 = (fun i j => raw13883step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13883step1 raw13883step0; decide +kernel
      have hl : raw13883step1Labels = raw13883step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13883step0 raw13883step0Labels permutation56 hz
    mixedMoment B raw13883step1 raw13883step1Labels = mixedMoment B raw13883step2 raw13883step2Labels := by
      have ha : raw13883step2 = (fun i j => raw13883step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13883step2 raw13883step1; decide +kernel
      have hl : raw13883step2Labels = raw13883step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13883step1 raw13883step1Labels permutation13 permutation7
    mixedMoment B raw13883step2 raw13883step2Labels = mixedMoment B raw13883step3 raw13883step3Labels := by
      have ha : raw13883step3 = -raw13883step2 := by apply Matrix.ext; change ∀ i j, raw13883step3 i j = -(raw13883step2 i j); unfold raw13883step3 raw13883step2; decide +kernel
      have hl : raw13883step3Labels = raw13883step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13883step3 raw13883step3Labels = mixedMoment B raw13883step4 raw13883step4Labels := by
      have ha : raw13883step4 = raw13883step3 := by apply Matrix.ext; unfold raw13883step4 raw13883step3; decide +kernel
      have hl : raw13883step3Labels = labelEmbedding10 ∘ raw13883step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13883step3 raw13883step3Labels raw13883step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw13884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13884 raw13884Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw13884 raw13884Labels = mixedMoment B raw13884step0 raw13884step0Labels := by
      have hz : ∀ j, raw13884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13884step0 = (fun i j => raw13884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13884step0 raw13884; decide +kernel
      have hl : raw13884step0Labels = raw13884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13884 raw13884Labels permutation346 hz
    mixedMoment B raw13884step0 raw13884step0Labels = mixedMoment B raw13884step1 raw13884step1Labels := by
      have ha : raw13884step1 = (fun i j => raw13884step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13884step1 raw13884step0; decide +kernel
      have hl : raw13884step1Labels = raw13884step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13884step0 raw13884step0Labels permutation51 permutation2
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw13885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13885 raw13885Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw13885 raw13885Labels = mixedMoment B raw13885step0 raw13885step0Labels := by
      have ha : raw13885step0 = (fun i j => raw13885 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13885step0 raw13885; decide +kernel
      have hl : raw13885step0Labels = raw13885Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13885 raw13885Labels permutation195 permutation2
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw13886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13886 raw13886Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw13886 raw13886Labels = mixedMoment B raw13886step0 raw13886step0Labels := by
      have hz : ∀ j, raw13886 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13886step0 = (fun i j => raw13886 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13886step0 raw13886; decide +kernel
      have hl : raw13886step0Labels = raw13886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13886 raw13886Labels permutation346 hz
    mixedMoment B raw13886step0 raw13886step0Labels = mixedMoment B raw13886step1 raw13886step1Labels := by
      have ha : raw13886step1 = (fun i j => raw13886step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13886step1 raw13886step0; decide +kernel
      have hl : raw13886step1Labels = raw13886step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13886step0 raw13886step0Labels permutation42 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw13887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13887 raw13887Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw13887 raw13887Labels = mixedMoment B raw13887step0 raw13887step0Labels := by
      have hz : ∀ j, raw13887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13887step0 = (fun i j => raw13887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13887step0 raw13887; decide +kernel
      have hl : raw13887step0Labels = raw13887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13887 raw13887Labels permutation346 hz
    mixedMoment B raw13887step0 raw13887step0Labels = mixedMoment B raw13887step1 raw13887step1Labels := by
      have ha : raw13887step1 = (fun i j => raw13887step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13887step1 raw13887step0; decide +kernel
      have hl : raw13887step1Labels = raw13887step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13887step0 raw13887step0Labels permutation48 permutation2
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw13888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13888 raw13888Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw13888 raw13888Labels = mixedMoment B raw13888step0 raw13888step0Labels := by
      have hz : ∀ j, raw13888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13888step0 = (fun i j => raw13888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13888step0 raw13888; decide +kernel
      have hl : raw13888step0Labels = raw13888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13888 raw13888Labels permutation346 hz
    mixedMoment B raw13888step0 raw13888step0Labels = mixedMoment B raw13888step1 raw13888step1Labels := by
      have ha : raw13888step1 = (fun i j => raw13888step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13888step1 raw13888step0; decide +kernel
      have hl : raw13888step1Labels = raw13888step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13888step0 raw13888step0Labels permutation51 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw13889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13889 raw13889Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw13889 raw13889Labels = mixedMoment B raw13889step0 raw13889step0Labels := by
      have hz : ∀ j, raw13889 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13889step0 = (fun i j => raw13889 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13889step0 raw13889; decide +kernel
      have hl : raw13889step0Labels = raw13889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13889 raw13889Labels permutation265 hz
    mixedMoment B raw13889step0 raw13889step0Labels = mixedMoment B raw13889step1 raw13889step1Labels := by
      have ha : raw13889step1 = (fun i j => raw13889step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13889step1 raw13889step0; decide +kernel
      have hl : raw13889step1Labels = raw13889step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13889step0 raw13889step0Labels permutation51 permutation2
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw13890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13890 raw13890Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw13890 raw13890Labels = mixedMoment B raw13890step0 raw13890step0Labels := by
      have ha : raw13890step0 = (fun i j => raw13890 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13890step0 raw13890; decide +kernel
      have hl : raw13890step0Labels = raw13890Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13890 raw13890Labels permutation171 permutation2
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw13891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13891 raw13891Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw13891 raw13891Labels = mixedMoment B raw13891step0 raw13891step0Labels := by
      have hz : ∀ j, raw13891 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13891step0 = (fun i j => raw13891 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13891step0 raw13891; decide +kernel
      have hl : raw13891step0Labels = raw13891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13891 raw13891Labels permutation265 hz
    mixedMoment B raw13891step0 raw13891step0Labels = mixedMoment B raw13891step1 raw13891step1Labels := by
      have ha : raw13891step1 = (fun i j => raw13891step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13891step1 raw13891step0; decide +kernel
      have hl : raw13891step1Labels = raw13891step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13891step0 raw13891step0Labels permutation42 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw13892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13892 raw13892Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw13892 raw13892Labels = mixedMoment B raw13892step0 raw13892step0Labels := by
      have hz : ∀ j, raw13892 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13892step0 = (fun i j => raw13892 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13892step0 raw13892; decide +kernel
      have hl : raw13892step0Labels = raw13892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13892 raw13892Labels permutation265 hz
    mixedMoment B raw13892step0 raw13892step0Labels = mixedMoment B raw13892step1 raw13892step1Labels := by
      have ha : raw13892step1 = (fun i j => raw13892step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13892step1 raw13892step0; decide +kernel
      have hl : raw13892step1Labels = raw13892step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13892step0 raw13892step0Labels permutation48 permutation2
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw13893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13893 raw13893Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw13893 raw13893Labels = mixedMoment B raw13893step0 raw13893step0Labels := by
      have hz : ∀ j, raw13893 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13893step0 = (fun i j => raw13893 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13893step0 raw13893; decide +kernel
      have hl : raw13893step0Labels = raw13893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13893 raw13893Labels permutation265 hz
    mixedMoment B raw13893step0 raw13893step0Labels = mixedMoment B raw13893step1 raw13893step1Labels := by
      have ha : raw13893step1 = (fun i j => raw13893step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13893step1 raw13893step0; decide +kernel
      have hl : raw13893step1Labels = raw13893step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13893step0 raw13893step0Labels permutation51 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw13894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13894 raw13894Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw13894 raw13894Labels = mixedMoment B raw13894step0 raw13894step0Labels := by
      have hz : ∀ j, raw13894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13894step0 = (fun i j => raw13894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13894step0 raw13894; decide +kernel
      have hl : raw13894step0Labels = raw13894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13894 raw13894Labels permutation346 hz
    mixedMoment B raw13894step0 raw13894step0Labels = mixedMoment B raw13894step1 raw13894step1Labels := by
      have hz : ∀ j, raw13894step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13894step1 = (fun i j => raw13894step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13894step1 raw13894step0; decide +kernel
      have hl : raw13894step1Labels = raw13894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13894step0 raw13894step0Labels permutation56 hz
    mixedMoment B raw13894step1 raw13894step1Labels = mixedMoment B raw13894step2 raw13894step2Labels := by
      have ha : raw13894step2 = (fun i j => raw13894step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13894step2 raw13894step1; decide +kernel
      have hl : raw13894step2Labels = raw13894step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13894step1 raw13894step1Labels permutation13 permutation2
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw13895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13895 raw13895Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw13895 raw13895Labels = mixedMoment B raw13895step0 raw13895step0Labels := by
      have hz : ∀ j, raw13895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13895step0 = (fun i j => raw13895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13895step0 raw13895; decide +kernel
      have hl : raw13895step0Labels = raw13895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13895 raw13895Labels permutation346 hz
    mixedMoment B raw13895step0 raw13895step0Labels = mixedMoment B raw13895step1 raw13895step1Labels := by
      have ha : raw13895step1 = (fun i j => raw13895step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13895step1 raw13895step0; decide +kernel
      have hl : raw13895step1Labels = raw13895step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13895step0 raw13895step0Labels permutation37 permutation2
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw13896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13896 raw13896Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw13896 raw13896Labels = mixedMoment B raw13896step0 raw13896step0Labels := by
      have hz : ∀ j, raw13896 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13896step0 = (fun i j => raw13896 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13896step0 raw13896; decide +kernel
      have hl : raw13896step0Labels = raw13896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13896 raw13896Labels permutation265 hz
    mixedMoment B raw13896step0 raw13896step0Labels = mixedMoment B raw13896step1 raw13896step1Labels := by
      have ha : raw13896step1 = (fun i j => raw13896step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13896step1 raw13896step0; decide +kernel
      have hl : raw13896step1Labels = raw13896step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13896step0 raw13896step0Labels permutation37 permutation2
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw13897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13897 raw13897Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw13897 raw13897Labels = mixedMoment B raw13897step0 raw13897step0Labels := by
      have hz : ∀ j, raw13897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13897step0 = (fun i j => raw13897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13897step0 raw13897; decide +kernel
      have hl : raw13897step0Labels = raw13897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13897 raw13897Labels permutation346 hz
    mixedMoment B raw13897step0 raw13897step0Labels = mixedMoment B raw13897step1 raw13897step1Labels := by
      have hz : ∀ j, raw13897step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13897step1 = (fun i j => raw13897step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13897step1 raw13897step0; decide +kernel
      have hl : raw13897step1Labels = raw13897step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13897step0 raw13897step0Labels permutation56 hz
    mixedMoment B raw13897step1 raw13897step1Labels = mixedMoment B raw13897step2 raw13897step2Labels := by
      have ha : raw13897step2 = (fun i j => raw13897step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13897step2 raw13897step1; decide +kernel
      have hl : raw13897step2Labels = raw13897step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13897step1 raw13897step1Labels permutation11 permutation2
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw13898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13898step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13898 raw13898Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw13898 raw13898Labels = mixedMoment B raw13898step0 raw13898step0Labels := by
      have hz : ∀ j, raw13898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13898step0 = (fun i j => raw13898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13898step0 raw13898; decide +kernel
      have hl : raw13898step0Labels = raw13898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13898 raw13898Labels permutation346 hz
    mixedMoment B raw13898step0 raw13898step0Labels = mixedMoment B raw13898step1 raw13898step1Labels := by
      have hz : ∀ j, raw13898step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13898step1 = (fun i j => raw13898step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13898step1 raw13898step0; decide +kernel
      have hl : raw13898step1Labels = raw13898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13898step0 raw13898step0Labels permutation56 hz
    mixedMoment B raw13898step1 raw13898step1Labels = mixedMoment B raw13898step2 raw13898step2Labels := by
      have ha : raw13898step2 = (fun i j => raw13898step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13898step2 raw13898step1; decide +kernel
      have hl : raw13898step2Labels = raw13898step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13898step1 raw13898step1Labels permutation13 permutation2
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw13899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13899step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13899 raw13899Labels = mixedMoment B node4620 node4620Labels := by
  calc
    mixedMoment B raw13899 raw13899Labels = mixedMoment B raw13899step0 raw13899step0Labels := by
      have hz : ∀ j, raw13899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13899step0 = (fun i j => raw13899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13899step0 raw13899; decide +kernel
      have hl : raw13899step0Labels = raw13899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13899 raw13899Labels permutation346 hz
    mixedMoment B raw13899step0 raw13899step0Labels = mixedMoment B raw13899step1 raw13899step1Labels := by
      have hz : ∀ j, raw13899step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13899step1 = (fun i j => raw13899step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13899step1 raw13899step0; decide +kernel
      have hl : raw13899step1Labels = raw13899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13899step0 raw13899step0Labels permutation56 hz
    mixedMoment B raw13899step1 raw13899step1Labels = mixedMoment B raw13899step2 raw13899step2Labels := by
      have ha : raw13899step2 = (fun i j => raw13899step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13899step2 raw13899step1; decide +kernel
      have hl : raw13899step2Labels = raw13899step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13899step1 raw13899step1Labels permutation12 permutation2
    _ = mixedMoment B node4620 node4620Labels := by rfl

def raw13900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13900 raw13900Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw13900 raw13900Labels = mixedMoment B raw13900step0 raw13900step0Labels := by
      have hz : ∀ j, raw13900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13900step0 = (fun i j => raw13900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13900step0 raw13900; decide +kernel
      have hl : raw13900step0Labels = raw13900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13900 raw13900Labels permutation346 hz
    mixedMoment B raw13900step0 raw13900step0Labels = mixedMoment B raw13900step1 raw13900step1Labels := by
      have ha : raw13900step1 = (fun i j => raw13900step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13900step1 raw13900step0; decide +kernel
      have hl : raw13900step1Labels = raw13900step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13900step0 raw13900step0Labels permutation36 permutation2
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw13901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13901 raw13901Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw13901 raw13901Labels = mixedMoment B raw13901step0 raw13901step0Labels := by
      have hz : ∀ j, raw13901 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13901step0 = (fun i j => raw13901 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13901step0 raw13901; decide +kernel
      have hl : raw13901step0Labels = raw13901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13901 raw13901Labels permutation265 hz
    mixedMoment B raw13901step0 raw13901step0Labels = mixedMoment B raw13901step1 raw13901step1Labels := by
      have ha : raw13901step1 = (fun i j => raw13901step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13901step1 raw13901step0; decide +kernel
      have hl : raw13901step1Labels = raw13901step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13901step0 raw13901step0Labels permutation36 permutation2
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw13902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13902step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw13902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13902 raw13902Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw13902 raw13902Labels = mixedMoment B raw13902step0 raw13902step0Labels := by
      have hz : ∀ j, raw13902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13902step0 = (fun i j => raw13902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13902step0 raw13902; decide +kernel
      have hl : raw13902step0Labels = raw13902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13902 raw13902Labels permutation346 hz
    mixedMoment B raw13902step0 raw13902step0Labels = mixedMoment B raw13902step1 raw13902step1Labels := by
      have hz : ∀ j, raw13902step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13902step1 = (fun i j => raw13902step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13902step1 raw13902step0; decide +kernel
      have hl : raw13902step1Labels = raw13902step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13902step0 raw13902step0Labels permutation56 hz
    mixedMoment B raw13902step1 raw13902step1Labels = mixedMoment B raw13902step2 raw13902step2Labels := by
      have ha : raw13902step2 = (fun i j => raw13902step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13902step2 raw13902step1; decide +kernel
      have hl : raw13902step2Labels = raw13902step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13902step1 raw13902step1Labels permutation9 permutation2
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw13903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13903step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13903 raw13903Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw13903 raw13903Labels = mixedMoment B raw13903step0 raw13903step0Labels := by
      have hz : ∀ j, raw13903 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13903step0 = (fun i j => raw13903 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13903step0 raw13903; decide +kernel
      have hl : raw13903step0Labels = raw13903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13903 raw13903Labels permutation346 hz
    mixedMoment B raw13903step0 raw13903step0Labels = mixedMoment B raw13903step1 raw13903step1Labels := by
      have hz : ∀ j, raw13903step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13903step1 = (fun i j => raw13903step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13903step1 raw13903step0; decide +kernel
      have hl : raw13903step1Labels = raw13903step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13903step0 raw13903step0Labels permutation56 hz
    mixedMoment B raw13903step1 raw13903step1Labels = mixedMoment B raw13903step2 raw13903step2Labels := by
      have ha : raw13903step2 = (fun i j => raw13903step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13903step2 raw13903step1; decide +kernel
      have hl : raw13903step2Labels = raw13903step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13903step1 raw13903step1Labels permutation12 permutation2
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw13904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13904step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13904step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13904step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13904 raw13904Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw13904 raw13904Labels = mixedMoment B raw13904step0 raw13904step0Labels := by
      have hz : ∀ j, raw13904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13904step0 = (fun i j => raw13904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13904step0 raw13904; decide +kernel
      have hl : raw13904step0Labels = raw13904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13904 raw13904Labels permutation346 hz
    mixedMoment B raw13904step0 raw13904step0Labels = mixedMoment B raw13904step1 raw13904step1Labels := by
      have hz : ∀ j, raw13904step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13904step1 = (fun i j => raw13904step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13904step1 raw13904step0; decide +kernel
      have hl : raw13904step1Labels = raw13904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13904step0 raw13904step0Labels permutation56 hz
    mixedMoment B raw13904step1 raw13904step1Labels = mixedMoment B raw13904step2 raw13904step2Labels := by
      have ha : raw13904step2 = (fun i j => raw13904step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13904step2 raw13904step1; decide +kernel
      have hl : raw13904step2Labels = raw13904step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13904step1 raw13904step1Labels permutation8 permutation3
    mixedMoment B raw13904step2 raw13904step2Labels = mixedMoment B raw13904step3 raw13904step3Labels := by
      have ha : raw13904step3 = raw13904step2 := by apply Matrix.ext; unfold raw13904step3 raw13904step2; decide +kernel
      have hl : raw13904step2Labels = labelEmbedding6 ∘ raw13904step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13904step2 raw13904step2Labels raw13904step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw13905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13905 raw13905Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw13905 raw13905Labels = mixedMoment B raw13905step0 raw13905step0Labels := by
      have hz : ∀ j, raw13905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13905step0 = (fun i j => raw13905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13905step0 raw13905; decide +kernel
      have hl : raw13905step0Labels = raw13905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13905 raw13905Labels permutation346 hz
    mixedMoment B raw13905step0 raw13905step0Labels = mixedMoment B raw13905step1 raw13905step1Labels := by
      have ha : raw13905step1 = (fun i j => raw13905step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13905step1 raw13905step0; decide +kernel
      have hl : raw13905step1Labels = raw13905step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13905step0 raw13905step0Labels permutation34 permutation2
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw13906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13906 raw13906Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw13906 raw13906Labels = mixedMoment B raw13906step0 raw13906step0Labels := by
      have hz : ∀ j, raw13906 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13906step0 = (fun i j => raw13906 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13906step0 raw13906; decide +kernel
      have hl : raw13906step0Labels = raw13906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13906 raw13906Labels permutation265 hz
    mixedMoment B raw13906step0 raw13906step0Labels = mixedMoment B raw13906step1 raw13906step1Labels := by
      have ha : raw13906step1 = (fun i j => raw13906step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13906step1 raw13906step0; decide +kernel
      have hl : raw13906step1Labels = raw13906step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13906step0 raw13906step0Labels permutation34 permutation2
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw13907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13907step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw13907step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw13907step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw13907step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13907 raw13907Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw13907 raw13907Labels = mixedMoment B raw13907step0 raw13907step0Labels := by
      have hz : ∀ j, raw13907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13907step0 = (fun i j => raw13907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13907step0 raw13907; decide +kernel
      have hl : raw13907step0Labels = raw13907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13907 raw13907Labels permutation346 hz
    mixedMoment B raw13907step0 raw13907step0Labels = mixedMoment B raw13907step1 raw13907step1Labels := by
      have hz : ∀ j, raw13907step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13907step1 = (fun i j => raw13907step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13907step1 raw13907step0; decide +kernel
      have hl : raw13907step1Labels = raw13907step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13907step0 raw13907step0Labels permutation56 hz
    mixedMoment B raw13907step1 raw13907step1Labels = mixedMoment B raw13907step2 raw13907step2Labels := by
      have ha : raw13907step2 = (fun i j => raw13907step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13907step2 raw13907step1; decide +kernel
      have hl : raw13907step2Labels = raw13907step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13907step1 raw13907step1Labels permutation30 permutation5
    mixedMoment B raw13907step2 raw13907step2Labels = mixedMoment B raw13907step3 raw13907step3Labels := by
      have ha : raw13907step3 = raw13907step2 := by apply Matrix.ext; unfold raw13907step3 raw13907step2; decide +kernel
      have hl : raw13907step2Labels = labelEmbedding8 ∘ raw13907step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13907step2 raw13907step2Labels raw13907step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw13908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13908step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13908 raw13908Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw13908 raw13908Labels = mixedMoment B raw13908step0 raw13908step0Labels := by
      have hz : ∀ j, raw13908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13908step0 = (fun i j => raw13908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13908step0 raw13908; decide +kernel
      have hl : raw13908step0Labels = raw13908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13908 raw13908Labels permutation346 hz
    mixedMoment B raw13908step0 raw13908step0Labels = mixedMoment B raw13908step1 raw13908step1Labels := by
      have hz : ∀ j, raw13908step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13908step1 = (fun i j => raw13908step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13908step1 raw13908step0; decide +kernel
      have hl : raw13908step1Labels = raw13908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13908step0 raw13908step0Labels permutation56 hz
    mixedMoment B raw13908step1 raw13908step1Labels = mixedMoment B raw13908step2 raw13908step2Labels := by
      have ha : raw13908step2 = (fun i j => raw13908step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13908step2 raw13908step1; decide +kernel
      have hl : raw13908step2Labels = raw13908step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13908step1 raw13908step1Labels permutation10 permutation2
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw13909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw13909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13909 raw13909Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw13909 raw13909Labels = mixedMoment B raw13909step0 raw13909step0Labels := by
      have hz : ∀ j, raw13909 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13909step0 = (fun i j => raw13909 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13909step0 raw13909; decide +kernel
      have hl : raw13909step0Labels = raw13909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13909 raw13909Labels permutation346 hz
    mixedMoment B raw13909step0 raw13909step0Labels = mixedMoment B raw13909step1 raw13909step1Labels := by
      have ha : raw13909step1 = (fun i j => raw13909step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13909step1 raw13909step0; decide +kernel
      have hl : raw13909step1Labels = raw13909step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13909step0 raw13909step0Labels permutation95 permutation6
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw13910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw13910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13910 raw13910Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw13910 raw13910Labels = mixedMoment B raw13910step0 raw13910step0Labels := by
      have hz : ∀ j, raw13910 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13910step0 = (fun i j => raw13910 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13910step0 raw13910; decide +kernel
      have hl : raw13910step0Labels = raw13910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13910 raw13910Labels permutation265 hz
    mixedMoment B raw13910step0 raw13910step0Labels = mixedMoment B raw13910step1 raw13910step1Labels := by
      have ha : raw13910step1 = (fun i j => raw13910step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13910step1 raw13910step0; decide +kernel
      have hl : raw13910step1Labels = raw13910step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13910step0 raw13910step0Labels permutation95 permutation6
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw13911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13911step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13911step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13911step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw13911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13911 raw13911Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw13911 raw13911Labels = mixedMoment B raw13911step0 raw13911step0Labels := by
      have hz : ∀ j, raw13911 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13911step0 = (fun i j => raw13911 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13911step0 raw13911; decide +kernel
      have hl : raw13911step0Labels = raw13911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13911 raw13911Labels permutation346 hz
    mixedMoment B raw13911step0 raw13911step0Labels = mixedMoment B raw13911step1 raw13911step1Labels := by
      have hz : ∀ j, raw13911step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13911step1 = (fun i j => raw13911step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13911step1 raw13911step0; decide +kernel
      have hl : raw13911step1Labels = raw13911step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13911step0 raw13911step0Labels permutation56 hz
    mixedMoment B raw13911step1 raw13911step1Labels = mixedMoment B raw13911step2 raw13911step2Labels := by
      have ha : raw13911step2 = (fun i j => raw13911step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13911step2 raw13911step1; decide +kernel
      have hl : raw13911step2Labels = raw13911step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13911step1 raw13911step1Labels permutation17 permutation6
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw13912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13912step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw13912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13912 raw13912Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw13912 raw13912Labels = mixedMoment B raw13912step0 raw13912step0Labels := by
      have hz : ∀ j, raw13912 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13912step0 = (fun i j => raw13912 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13912step0 raw13912; decide +kernel
      have hl : raw13912step0Labels = raw13912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13912 raw13912Labels permutation346 hz
    mixedMoment B raw13912step0 raw13912step0Labels = mixedMoment B raw13912step1 raw13912step1Labels := by
      have hz : ∀ j, raw13912step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13912step1 = (fun i j => raw13912step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13912step1 raw13912step0; decide +kernel
      have hl : raw13912step1Labels = raw13912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13912step0 raw13912step0Labels permutation56 hz
    mixedMoment B raw13912step1 raw13912step1Labels = mixedMoment B raw13912step2 raw13912step2Labels := by
      have ha : raw13912step2 = (fun i j => raw13912step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13912step2 raw13912step1; decide +kernel
      have hl : raw13912step2Labels = raw13912step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13912step1 raw13912step1Labels permutation17 permutation6
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw13913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13913step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13913 raw13913Labels = mixedMoment B node4001 node4001Labels := by
  calc
    mixedMoment B raw13913 raw13913Labels = mixedMoment B raw13913step0 raw13913step0Labels := by
      have hz : ∀ j, raw13913 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13913step0 = (fun i j => raw13913 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13913step0 raw13913; decide +kernel
      have hl : raw13913step0Labels = raw13913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13913 raw13913Labels permutation346 hz
    mixedMoment B raw13913step0 raw13913step0Labels = mixedMoment B raw13913step1 raw13913step1Labels := by
      have hz : ∀ j, raw13913step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13913step1 = (fun i j => raw13913step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13913step1 raw13913step0; decide +kernel
      have hl : raw13913step1Labels = raw13913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13913step0 raw13913step0Labels permutation56 hz
    mixedMoment B raw13913step1 raw13913step1Labels = mixedMoment B raw13913step2 raw13913step2Labels := by
      have ha : raw13913step2 = (fun i j => raw13913step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13913step2 raw13913step1; decide +kernel
      have hl : raw13913step2Labels = raw13913step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13913step1 raw13913step1Labels permutation17 permutation6
    _ = mixedMoment B node4001 node4001Labels := by rfl

def raw13914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13914step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13914 raw13914Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw13914 raw13914Labels = mixedMoment B raw13914step0 raw13914step0Labels := by
      have hz : ∀ j, raw13914 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13914step0 = (fun i j => raw13914 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13914step0 raw13914; decide +kernel
      have hl : raw13914step0Labels = raw13914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13914 raw13914Labels permutation346 hz
    mixedMoment B raw13914step0 raw13914step0Labels = mixedMoment B raw13914step1 raw13914step1Labels := by
      have ha : raw13914step1 = (fun i j => raw13914step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13914step1 raw13914step0; decide +kernel
      have hl : raw13914step1Labels = raw13914step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13914step0 raw13914step0Labels permutation40 permutation3
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw13915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13915 raw13915Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw13915 raw13915Labels = mixedMoment B raw13915step0 raw13915step0Labels := by
      have ha : raw13915step0 = (fun i j => raw13915 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13915step0 raw13915; decide +kernel
      have hl : raw13915step0Labels = raw13915Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13915 raw13915Labels permutation184 permutation3
    _ = mixedMoment B node2951 node2951Labels := by rfl

def raw13916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13916step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13916 raw13916Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw13916 raw13916Labels = mixedMoment B raw13916step0 raw13916step0Labels := by
      have hz : ∀ j, raw13916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13916step0 = (fun i j => raw13916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13916step0 raw13916; decide +kernel
      have hl : raw13916step0Labels = raw13916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13916 raw13916Labels permutation346 hz
    mixedMoment B raw13916step0 raw13916step0Labels = mixedMoment B raw13916step1 raw13916step1Labels := by
      have ha : raw13916step1 = (fun i j => raw13916step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13916step1 raw13916step0; decide +kernel
      have hl : raw13916step1Labels = raw13916step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13916step0 raw13916step0Labels permutation40 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw13917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13917 raw13917Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw13917 raw13917Labels = mixedMoment B raw13917step0 raw13917step0Labels := by
      have hz : ∀ j, raw13917 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13917step0 = (fun i j => raw13917 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13917step0 raw13917; decide +kernel
      have hl : raw13917step0Labels = raw13917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13917 raw13917Labels permutation346 hz
    mixedMoment B raw13917step0 raw13917step0Labels = mixedMoment B raw13917step1 raw13917step1Labels := by
      have ha : raw13917step1 = (fun i j => raw13917step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13917step1 raw13917step0; decide +kernel
      have hl : raw13917step1Labels = raw13917step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13917step0 raw13917step0Labels permutation46 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw13918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13918step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13918 raw13918Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw13918 raw13918Labels = mixedMoment B raw13918step0 raw13918step0Labels := by
      have hz : ∀ j, raw13918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13918step0 = (fun i j => raw13918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13918step0 raw13918; decide +kernel
      have hl : raw13918step0Labels = raw13918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13918 raw13918Labels permutation346 hz
    mixedMoment B raw13918step0 raw13918step0Labels = mixedMoment B raw13918step1 raw13918step1Labels := by
      have ha : raw13918step1 = (fun i j => raw13918step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13918step1 raw13918step0; decide +kernel
      have hl : raw13918step1Labels = raw13918step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13918step0 raw13918step0Labels permutation53 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw13919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13919step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13919 raw13919Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw13919 raw13919Labels = mixedMoment B raw13919step0 raw13919step0Labels := by
      have hz : ∀ j, raw13919 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13919step0 = (fun i j => raw13919 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13919step0 raw13919; decide +kernel
      have hl : raw13919step0Labels = raw13919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13919 raw13919Labels permutation265 hz
    mixedMoment B raw13919step0 raw13919step0Labels = mixedMoment B raw13919step1 raw13919step1Labels := by
      have ha : raw13919step1 = (fun i j => raw13919step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13919step1 raw13919step0; decide +kernel
      have hl : raw13919step1Labels = raw13919step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13919step0 raw13919step0Labels permutation40 permutation3
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw13920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13920 raw13920Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw13920 raw13920Labels = mixedMoment B raw13920step0 raw13920step0Labels := by
      have ha : raw13920step0 = (fun i j => raw13920 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13920step0 raw13920; decide +kernel
      have hl : raw13920step0Labels = raw13920Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13920 raw13920Labels permutation160 permutation3
    _ = mixedMoment B node2951 node2951Labels := by rfl

def raw13921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13921step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13921 raw13921Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw13921 raw13921Labels = mixedMoment B raw13921step0 raw13921step0Labels := by
      have hz : ∀ j, raw13921 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13921step0 = (fun i j => raw13921 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13921step0 raw13921; decide +kernel
      have hl : raw13921step0Labels = raw13921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13921 raw13921Labels permutation265 hz
    mixedMoment B raw13921step0 raw13921step0Labels = mixedMoment B raw13921step1 raw13921step1Labels := by
      have ha : raw13921step1 = (fun i j => raw13921step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13921step1 raw13921step0; decide +kernel
      have hl : raw13921step1Labels = raw13921step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13921step0 raw13921step0Labels permutation40 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw13922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13922 raw13922Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw13922 raw13922Labels = mixedMoment B raw13922step0 raw13922step0Labels := by
      have hz : ∀ j, raw13922 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13922step0 = (fun i j => raw13922 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13922step0 raw13922; decide +kernel
      have hl : raw13922step0Labels = raw13922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13922 raw13922Labels permutation265 hz
    mixedMoment B raw13922step0 raw13922step0Labels = mixedMoment B raw13922step1 raw13922step1Labels := by
      have ha : raw13922step1 = (fun i j => raw13922step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13922step1 raw13922step0; decide +kernel
      have hl : raw13922step1Labels = raw13922step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13922step0 raw13922step0Labels permutation46 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw13923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13923 raw13923Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw13923 raw13923Labels = mixedMoment B raw13923step0 raw13923step0Labels := by
      have hz : ∀ j, raw13923 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13923step0 = (fun i j => raw13923 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13923step0 raw13923; decide +kernel
      have hl : raw13923step0Labels = raw13923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13923 raw13923Labels permutation265 hz
    mixedMoment B raw13923step0 raw13923step0Labels = mixedMoment B raw13923step1 raw13923step1Labels := by
      have ha : raw13923step1 = (fun i j => raw13923step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13923step1 raw13923step0; decide +kernel
      have hl : raw13923step1Labels = raw13923step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13923step0 raw13923step0Labels permutation53 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw13924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13924step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13924step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw13924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13924 raw13924Labels = mixedMoment B node1302 node1302Labels := by
  calc
    mixedMoment B raw13924 raw13924Labels = mixedMoment B raw13924step0 raw13924step0Labels := by
      have hz : ∀ j, raw13924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13924step0 = (fun i j => raw13924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13924step0 raw13924; decide +kernel
      have hl : raw13924step0Labels = raw13924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13924 raw13924Labels permutation346 hz
    mixedMoment B raw13924step0 raw13924step0Labels = mixedMoment B raw13924step1 raw13924step1Labels := by
      have hz : ∀ j, raw13924step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13924step1 = (fun i j => raw13924step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13924step1 raw13924step0; decide +kernel
      have hl : raw13924step1Labels = raw13924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13924step0 raw13924step0Labels permutation56 hz
    mixedMoment B raw13924step1 raw13924step1Labels = mixedMoment B raw13924step2 raw13924step2Labels := by
      have ha : raw13924step2 = (fun i j => raw13924step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13924step2 raw13924step1; decide +kernel
      have hl : raw13924step2Labels = raw13924step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13924step1 raw13924step1Labels permutation11 permutation3
    _ = mixedMoment B node1302 node1302Labels := by rfl

def raw13925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13925step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw13925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13925 raw13925Labels = mixedMoment B node2961 node2961Labels := by
  calc
    mixedMoment B raw13925 raw13925Labels = mixedMoment B raw13925step0 raw13925step0Labels := by
      have hz : ∀ j, raw13925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13925step0 = (fun i j => raw13925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13925step0 raw13925; decide +kernel
      have hl : raw13925step0Labels = raw13925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13925 raw13925Labels permutation346 hz
    mixedMoment B raw13925step0 raw13925step0Labels = mixedMoment B raw13925step1 raw13925step1Labels := by
      have ha : raw13925step1 = (fun i j => raw13925step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13925step1 raw13925step0; decide +kernel
      have hl : raw13925step1Labels = raw13925step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13925step0 raw13925step0Labels permutation35 permutation3
    _ = mixedMoment B node2961 node2961Labels := by rfl

def raw13926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw13926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13926 raw13926Labels = mixedMoment B node2961 node2961Labels := by
  calc
    mixedMoment B raw13926 raw13926Labels = mixedMoment B raw13926step0 raw13926step0Labels := by
      have hz : ∀ j, raw13926 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13926step0 = (fun i j => raw13926 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13926step0 raw13926; decide +kernel
      have hl : raw13926step0Labels = raw13926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13926 raw13926Labels permutation265 hz
    mixedMoment B raw13926step0 raw13926step0Labels = mixedMoment B raw13926step1 raw13926step1Labels := by
      have ha : raw13926step1 = (fun i j => raw13926step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13926step1 raw13926step0; decide +kernel
      have hl : raw13926step1Labels = raw13926step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13926step0 raw13926step0Labels permutation35 permutation3
    _ = mixedMoment B node2961 node2961Labels := by rfl

def raw13927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13927step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13927step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13927step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw13927step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13927 raw13927Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw13927 raw13927Labels = mixedMoment B raw13927step0 raw13927step0Labels := by
      have hz : ∀ j, raw13927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13927step0 = (fun i j => raw13927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13927step0 raw13927; decide +kernel
      have hl : raw13927step0Labels = raw13927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13927 raw13927Labels permutation346 hz
    mixedMoment B raw13927step0 raw13927step0Labels = mixedMoment B raw13927step1 raw13927step1Labels := by
      have hz : ∀ j, raw13927step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13927step1 = (fun i j => raw13927step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13927step1 raw13927step0; decide +kernel
      have hl : raw13927step1Labels = raw13927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13927step0 raw13927step0Labels permutation56 hz
    mixedMoment B raw13927step1 raw13927step1Labels = mixedMoment B raw13927step2 raw13927step2Labels := by
      have ha : raw13927step2 = (fun i j => raw13927step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13927step2 raw13927step1; decide +kernel
      have hl : raw13927step2Labels = raw13927step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13927step1 raw13927step1Labels permutation11 permutation3
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw13928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13928step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13928step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13928step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13928step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13928 raw13928Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw13928 raw13928Labels = mixedMoment B raw13928step0 raw13928step0Labels := by
      have hz : ∀ j, raw13928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13928step0 = (fun i j => raw13928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13928step0 raw13928; decide +kernel
      have hl : raw13928step0Labels = raw13928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13928 raw13928Labels permutation346 hz
    mixedMoment B raw13928step0 raw13928step0Labels = mixedMoment B raw13928step1 raw13928step1Labels := by
      have hz : ∀ j, raw13928step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13928step1 = (fun i j => raw13928step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13928step1 raw13928step0; decide +kernel
      have hl : raw13928step1Labels = raw13928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13928step0 raw13928step0Labels permutation56 hz
    mixedMoment B raw13928step1 raw13928step1Labels = mixedMoment B raw13928step2 raw13928step2Labels := by
      have ha : raw13928step2 = (fun i j => raw13928step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13928step2 raw13928step1; decide +kernel
      have hl : raw13928step2Labels = raw13928step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13928step1 raw13928step1Labels permutation13 permutation3
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw13929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13929step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13929step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13929step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13929 raw13929Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw13929 raw13929Labels = mixedMoment B raw13929step0 raw13929step0Labels := by
      have hz : ∀ j, raw13929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13929step0 = (fun i j => raw13929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13929step0 raw13929; decide +kernel
      have hl : raw13929step0Labels = raw13929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13929 raw13929Labels permutation346 hz
    mixedMoment B raw13929step0 raw13929step0Labels = mixedMoment B raw13929step1 raw13929step1Labels := by
      have hz : ∀ j, raw13929step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13929step1 = (fun i j => raw13929step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13929step1 raw13929step0; decide +kernel
      have hl : raw13929step1Labels = raw13929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13929step0 raw13929step0Labels permutation56 hz
    mixedMoment B raw13929step1 raw13929step1Labels = mixedMoment B raw13929step2 raw13929step2Labels := by
      have ha : raw13929step2 = (fun i j => raw13929step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13929step2 raw13929step1; decide +kernel
      have hl : raw13929step2Labels = raw13929step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13929step1 raw13929step1Labels permutation9 permutation3
    _ = mixedMoment B node1295 node1295Labels := by rfl

def raw13930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13930step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13930 raw13930Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw13930 raw13930Labels = mixedMoment B raw13930step0 raw13930step0Labels := by
      have hz : ∀ j, raw13930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13930step0 = (fun i j => raw13930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13930step0 raw13930; decide +kernel
      have hl : raw13930step0Labels = raw13930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13930 raw13930Labels permutation346 hz
    mixedMoment B raw13930step0 raw13930step0Labels = mixedMoment B raw13930step1 raw13930step1Labels := by
      have ha : raw13930step1 = (fun i j => raw13930step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13930step1 raw13930step0; decide +kernel
      have hl : raw13930step1Labels = raw13930step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13930step0 raw13930step0Labels permutation33 permutation3
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw13931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13931 raw13931Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw13931 raw13931Labels = mixedMoment B raw13931step0 raw13931step0Labels := by
      have hz : ∀ j, raw13931 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13931step0 = (fun i j => raw13931 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13931step0 raw13931; decide +kernel
      have hl : raw13931step0Labels = raw13931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13931 raw13931Labels permutation265 hz
    mixedMoment B raw13931step0 raw13931step0Labels = mixedMoment B raw13931step1 raw13931step1Labels := by
      have ha : raw13931step1 = (fun i j => raw13931step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13931step1 raw13931step0; decide +kernel
      have hl : raw13931step1Labels = raw13931step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13931step0 raw13931step0Labels permutation33 permutation3
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw13932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13932step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw13932step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13932 raw13932Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw13932 raw13932Labels = mixedMoment B raw13932step0 raw13932step0Labels := by
      have hz : ∀ j, raw13932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13932step0 = (fun i j => raw13932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13932step0 raw13932; decide +kernel
      have hl : raw13932step0Labels = raw13932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13932 raw13932Labels permutation346 hz
    mixedMoment B raw13932step0 raw13932step0Labels = mixedMoment B raw13932step1 raw13932step1Labels := by
      have hz : ∀ j, raw13932step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13932step1 = (fun i j => raw13932step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13932step1 raw13932step0; decide +kernel
      have hl : raw13932step1Labels = raw13932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13932step0 raw13932step0Labels permutation56 hz
    mixedMoment B raw13932step1 raw13932step1Labels = mixedMoment B raw13932step2 raw13932step2Labels := by
      have ha : raw13932step2 = (fun i j => raw13932step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13932step2 raw13932step1; decide +kernel
      have hl : raw13932step2Labels = raw13932step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13932step1 raw13932step1Labels permutation9 permutation3
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw13933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13933step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13933 raw13933Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw13933 raw13933Labels = mixedMoment B raw13933step0 raw13933step0Labels := by
      have hz : ∀ j, raw13933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13933step0 = (fun i j => raw13933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13933step0 raw13933; decide +kernel
      have hl : raw13933step0Labels = raw13933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13933 raw13933Labels permutation346 hz
    mixedMoment B raw13933step0 raw13933step0Labels = mixedMoment B raw13933step1 raw13933step1Labels := by
      have hz : ∀ j, raw13933step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13933step1 = (fun i j => raw13933step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13933step1 raw13933step0; decide +kernel
      have hl : raw13933step1Labels = raw13933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13933step0 raw13933step0Labels permutation56 hz
    mixedMoment B raw13933step1 raw13933step1Labels = mixedMoment B raw13933step2 raw13933step2Labels := by
      have ha : raw13933step2 = (fun i j => raw13933step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13933step2 raw13933step1; decide +kernel
      have hl : raw13933step2Labels = raw13933step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13933step1 raw13933step1Labels permutation12 permutation3
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw13934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13934step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13934 raw13934Labels = mixedMoment B node1292 node1292Labels := by
  calc
    mixedMoment B raw13934 raw13934Labels = mixedMoment B raw13934step0 raw13934step0Labels := by
      have hz : ∀ j, raw13934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13934step0 = (fun i j => raw13934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13934step0 raw13934; decide +kernel
      have hl : raw13934step0Labels = raw13934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13934 raw13934Labels permutation346 hz
    mixedMoment B raw13934step0 raw13934step0Labels = mixedMoment B raw13934step1 raw13934step1Labels := by
      have hz : ∀ j, raw13934step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13934step1 = (fun i j => raw13934step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13934step1 raw13934step0; decide +kernel
      have hl : raw13934step1Labels = raw13934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13934step0 raw13934step0Labels permutation56 hz
    mixedMoment B raw13934step1 raw13934step1Labels = mixedMoment B raw13934step2 raw13934step2Labels := by
      have ha : raw13934step2 = (fun i j => raw13934step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13934step2 raw13934step1; decide +kernel
      have hl : raw13934step2Labels = raw13934step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13934step1 raw13934step1Labels permutation8 permutation3
    _ = mixedMoment B node1292 node1292Labels := by rfl

def raw13935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13935 raw13935Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw13935 raw13935Labels = mixedMoment B raw13935step0 raw13935step0Labels := by
      have hz : ∀ j, raw13935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13935step0 = (fun i j => raw13935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13935step0 raw13935; decide +kernel
      have hl : raw13935step0Labels = raw13935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13935 raw13935Labels permutation346 hz
    mixedMoment B raw13935step0 raw13935step0Labels = mixedMoment B raw13935step1 raw13935step1Labels := by
      have ha : raw13935step1 = (fun i j => raw13935step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13935step1 raw13935step0; decide +kernel
      have hl : raw13935step1Labels = raw13935step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13935step0 raw13935step0Labels permutation32 permutation3
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw13936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13936 raw13936Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw13936 raw13936Labels = mixedMoment B raw13936step0 raw13936step0Labels := by
      have hz : ∀ j, raw13936 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13936step0 = (fun i j => raw13936 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13936step0 raw13936; decide +kernel
      have hl : raw13936step0Labels = raw13936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13936 raw13936Labels permutation265 hz
    mixedMoment B raw13936step0 raw13936step0Labels = mixedMoment B raw13936step1 raw13936step1Labels := by
      have ha : raw13936step1 = (fun i j => raw13936step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13936step1 raw13936step0; decide +kernel
      have hl : raw13936step1Labels = raw13936step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13936step0 raw13936step0Labels permutation32 permutation3
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw13937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13937step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13937step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw13937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13937 raw13937Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw13937 raw13937Labels = mixedMoment B raw13937step0 raw13937step0Labels := by
      have hz : ∀ j, raw13937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13937step0 = (fun i j => raw13937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13937step0 raw13937; decide +kernel
      have hl : raw13937step0Labels = raw13937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13937 raw13937Labels permutation346 hz
    mixedMoment B raw13937step0 raw13937step0Labels = mixedMoment B raw13937step1 raw13937step1Labels := by
      have hz : ∀ j, raw13937step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13937step1 = (fun i j => raw13937step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13937step1 raw13937step0; decide +kernel
      have hl : raw13937step1Labels = raw13937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13937step0 raw13937step0Labels permutation56 hz
    mixedMoment B raw13937step1 raw13937step1Labels = mixedMoment B raw13937step2 raw13937step2Labels := by
      have ha : raw13937step2 = (fun i j => raw13937step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13937step2 raw13937step1; decide +kernel
      have hl : raw13937step2Labels = raw13937step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13937step1 raw13937step1Labels permutation8 permutation3
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw13938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13938step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw13938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13938 raw13938Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw13938 raw13938Labels = mixedMoment B raw13938step0 raw13938step0Labels := by
      have hz : ∀ j, raw13938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13938step0 = (fun i j => raw13938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13938step0 raw13938; decide +kernel
      have hl : raw13938step0Labels = raw13938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13938 raw13938Labels permutation346 hz
    mixedMoment B raw13938step0 raw13938step0Labels = mixedMoment B raw13938step1 raw13938step1Labels := by
      have hz : ∀ j, raw13938step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13938step1 = (fun i j => raw13938step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13938step1 raw13938step0; decide +kernel
      have hl : raw13938step1Labels = raw13938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13938step0 raw13938step0Labels permutation56 hz
    mixedMoment B raw13938step1 raw13938step1Labels = mixedMoment B raw13938step2 raw13938step2Labels := by
      have ha : raw13938step2 = (fun i j => raw13938step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13938step2 raw13938step1; decide +kernel
      have hl : raw13938step2Labels = raw13938step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13938step1 raw13938step1Labels permutation10 permutation3
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw13939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13939step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13939 raw13939Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw13939 raw13939Labels = mixedMoment B raw13939step0 raw13939step0Labels := by
      have hz : ∀ j, raw13939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13939step0 = (fun i j => raw13939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13939step0 raw13939; decide +kernel
      have hl : raw13939step0Labels = raw13939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13939 raw13939Labels permutation346 hz
    mixedMoment B raw13939step0 raw13939step0Labels = mixedMoment B raw13939step1 raw13939step1Labels := by
      have ha : raw13939step1 = (fun i j => raw13939step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13939step1 raw13939step0; decide +kernel
      have hl : raw13939step1Labels = raw13939step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13939step0 raw13939step0Labels permutation51 permutation7
    mixedMoment B raw13939step1 raw13939step1Labels = mixedMoment B raw13939step2 raw13939step2Labels := by
      have ha : raw13939step2 = -raw13939step1 := by apply Matrix.ext; change ∀ i j, raw13939step2 i j = -(raw13939step1 i j); unfold raw13939step2 raw13939step1; decide +kernel
      have hl : raw13939step2Labels = raw13939step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13939step2 raw13939step2Labels = mixedMoment B raw13939step3 raw13939step3Labels := by
      have ha : raw13939step3 = raw13939step2 := by apply Matrix.ext; unfold raw13939step3 raw13939step2; decide +kernel
      have hl : raw13939step2Labels = labelEmbedding1 ∘ raw13939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13939step2 raw13939step2Labels raw13939step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw13940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13940step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13940step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13940step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13940step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13940 raw13940Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw13940 raw13940Labels = mixedMoment B raw13940step0 raw13940step0Labels := by
      have hz : ∀ j, raw13940 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13940step0 = (fun i j => raw13940 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13940step0 raw13940; decide +kernel
      have hl : raw13940step0Labels = raw13940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13940 raw13940Labels permutation265 hz
    mixedMoment B raw13940step0 raw13940step0Labels = mixedMoment B raw13940step1 raw13940step1Labels := by
      have ha : raw13940step1 = (fun i j => raw13940step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13940step1 raw13940step0; decide +kernel
      have hl : raw13940step1Labels = raw13940step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13940step0 raw13940step0Labels permutation51 permutation7
    mixedMoment B raw13940step1 raw13940step1Labels = mixedMoment B raw13940step2 raw13940step2Labels := by
      have ha : raw13940step2 = -raw13940step1 := by apply Matrix.ext; change ∀ i j, raw13940step2 i j = -(raw13940step1 i j); unfold raw13940step2 raw13940step1; decide +kernel
      have hl : raw13940step2Labels = raw13940step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13940step2 raw13940step2Labels = mixedMoment B raw13940step3 raw13940step3Labels := by
      have ha : raw13940step3 = raw13940step2 := by apply Matrix.ext; unfold raw13940step3 raw13940step2; decide +kernel
      have hl : raw13940step2Labels = labelEmbedding1 ∘ raw13940step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13940step2 raw13940step2Labels raw13940step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw13941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13941step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13941step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13941step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13941step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13941step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13941step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13941step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13941 raw13941Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw13941 raw13941Labels = mixedMoment B raw13941step0 raw13941step0Labels := by
      have hz : ∀ j, raw13941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13941step0 = (fun i j => raw13941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13941step0 raw13941; decide +kernel
      have hl : raw13941step0Labels = raw13941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13941 raw13941Labels permutation346 hz
    mixedMoment B raw13941step0 raw13941step0Labels = mixedMoment B raw13941step1 raw13941step1Labels := by
      have hz : ∀ j, raw13941step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13941step1 = (fun i j => raw13941step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13941step1 raw13941step0; decide +kernel
      have hl : raw13941step1Labels = raw13941step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13941step0 raw13941step0Labels permutation56 hz
    mixedMoment B raw13941step1 raw13941step1Labels = mixedMoment B raw13941step2 raw13941step2Labels := by
      have ha : raw13941step2 = (fun i j => raw13941step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13941step2 raw13941step1; decide +kernel
      have hl : raw13941step2Labels = raw13941step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13941step1 raw13941step1Labels permutation13 permutation7
    mixedMoment B raw13941step2 raw13941step2Labels = mixedMoment B raw13941step3 raw13941step3Labels := by
      have ha : raw13941step3 = -raw13941step2 := by apply Matrix.ext; change ∀ i j, raw13941step3 i j = -(raw13941step2 i j); unfold raw13941step3 raw13941step2; decide +kernel
      have hl : raw13941step3Labels = raw13941step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13941step3 raw13941step3Labels = mixedMoment B raw13941step4 raw13941step4Labels := by
      have ha : raw13941step4 = raw13941step3 := by apply Matrix.ext; unfold raw13941step4 raw13941step3; decide +kernel
      have hl : raw13941step3Labels = labelEmbedding1 ∘ raw13941step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13941step3 raw13941step3Labels raw13941step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw13942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13942step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13942step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13942step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13942step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13942step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13942 raw13942Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw13942 raw13942Labels = mixedMoment B raw13942step0 raw13942step0Labels := by
      have hz : ∀ j, raw13942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13942step0 = (fun i j => raw13942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13942step0 raw13942; decide +kernel
      have hl : raw13942step0Labels = raw13942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13942 raw13942Labels permutation346 hz
    mixedMoment B raw13942step0 raw13942step0Labels = mixedMoment B raw13942step1 raw13942step1Labels := by
      have hz : ∀ j, raw13942step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13942step1 = (fun i j => raw13942step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13942step1 raw13942step0; decide +kernel
      have hl : raw13942step1Labels = raw13942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13942step0 raw13942step0Labels permutation56 hz
    mixedMoment B raw13942step1 raw13942step1Labels = mixedMoment B raw13942step2 raw13942step2Labels := by
      have ha : raw13942step2 = (fun i j => raw13942step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13942step2 raw13942step1; decide +kernel
      have hl : raw13942step2Labels = raw13942step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13942step1 raw13942step1Labels permutation13 permutation7
    mixedMoment B raw13942step2 raw13942step2Labels = mixedMoment B raw13942step3 raw13942step3Labels := by
      have ha : raw13942step3 = -raw13942step2 := by apply Matrix.ext; change ∀ i j, raw13942step3 i j = -(raw13942step2 i j); unfold raw13942step3 raw13942step2; decide +kernel
      have hl : raw13942step3Labels = raw13942step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13942step3 raw13942step3Labels = mixedMoment B raw13942step4 raw13942step4Labels := by
      have ha : raw13942step4 = raw13942step3 := by apply Matrix.ext; unfold raw13942step4 raw13942step3; decide +kernel
      have hl : raw13942step3Labels = labelEmbedding1 ∘ raw13942step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13942step3 raw13942step3Labels raw13942step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw13943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13943step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13943step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13943step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13943step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13943step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13943 raw13943Labels = mixedMoment B node3861 node3861Labels := by
  calc
    mixedMoment B raw13943 raw13943Labels = mixedMoment B raw13943step0 raw13943step0Labels := by
      have hz : ∀ j, raw13943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13943step0 = (fun i j => raw13943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13943step0 raw13943; decide +kernel
      have hl : raw13943step0Labels = raw13943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13943 raw13943Labels permutation346 hz
    mixedMoment B raw13943step0 raw13943step0Labels = mixedMoment B raw13943step1 raw13943step1Labels := by
      have hz : ∀ j, raw13943step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13943step1 = (fun i j => raw13943step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13943step1 raw13943step0; decide +kernel
      have hl : raw13943step1Labels = raw13943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13943step0 raw13943step0Labels permutation56 hz
    mixedMoment B raw13943step1 raw13943step1Labels = mixedMoment B raw13943step2 raw13943step2Labels := by
      have ha : raw13943step2 = (fun i j => raw13943step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13943step2 raw13943step1; decide +kernel
      have hl : raw13943step2Labels = raw13943step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13943step1 raw13943step1Labels permutation13 permutation7
    mixedMoment B raw13943step2 raw13943step2Labels = mixedMoment B raw13943step3 raw13943step3Labels := by
      have ha : raw13943step3 = -raw13943step2 := by apply Matrix.ext; change ∀ i j, raw13943step3 i j = -(raw13943step2 i j); unfold raw13943step3 raw13943step2; decide +kernel
      have hl : raw13943step3Labels = raw13943step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13943step3 raw13943step3Labels = mixedMoment B raw13943step4 raw13943step4Labels := by
      have ha : raw13943step4 = raw13943step3 := by apply Matrix.ext; unfold raw13943step4 raw13943step3; decide +kernel
      have hl : raw13943step3Labels = labelEmbedding1 ∘ raw13943step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13943step3 raw13943step3Labels raw13943step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3861 node3861Labels := by rfl

def raw13944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13944step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13944step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13944step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13944step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13944 raw13944Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw13944 raw13944Labels = mixedMoment B raw13944step0 raw13944step0Labels := by
      have hz : ∀ j, raw13944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13944step0 = (fun i j => raw13944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13944step0 raw13944; decide +kernel
      have hl : raw13944step0Labels = raw13944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13944 raw13944Labels permutation346 hz
    mixedMoment B raw13944step0 raw13944step0Labels = mixedMoment B raw13944step1 raw13944step1Labels := by
      have ha : raw13944step1 = (fun i j => raw13944step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13944step1 raw13944step0; decide +kernel
      have hl : raw13944step1Labels = raw13944step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13944step0 raw13944step0Labels permutation40 permutation5
    mixedMoment B raw13944step1 raw13944step1Labels = mixedMoment B raw13944step2 raw13944step2Labels := by
      have ha : raw13944step2 = -raw13944step1 := by apply Matrix.ext; change ∀ i j, raw13944step2 i j = -(raw13944step1 i j); unfold raw13944step2 raw13944step1; decide +kernel
      have hl : raw13944step2Labels = raw13944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13944step2 raw13944step2Labels = mixedMoment B raw13944step3 raw13944step3Labels := by
      have ha : raw13944step3 = raw13944step2 := by apply Matrix.ext; unfold raw13944step3 raw13944step2; decide +kernel
      have hl : raw13944step2Labels = labelEmbedding1 ∘ raw13944step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13944step2 raw13944step2Labels raw13944step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

def raw13945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13945step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13945step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13945 raw13945Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw13945 raw13945Labels = mixedMoment B raw13945step0 raw13945step0Labels := by
      have ha : raw13945step0 = (fun i j => raw13945 (permutation253 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13945step0 raw13945; decide +kernel
      have hl : raw13945step0Labels = raw13945Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13945 raw13945Labels permutation253 permutation7
    mixedMoment B raw13945step0 raw13945step0Labels = mixedMoment B raw13945step1 raw13945step1Labels := by
      have ha : raw13945step1 = -raw13945step0 := by apply Matrix.ext; change ∀ i j, raw13945step1 i j = -(raw13945step0 i j); unfold raw13945step1 raw13945step0; decide +kernel
      have hl : raw13945step1Labels = raw13945step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13945step1 raw13945step1Labels = mixedMoment B raw13945step2 raw13945step2Labels := by
      have ha : raw13945step2 = raw13945step1 := by apply Matrix.ext; unfold raw13945step2 raw13945step1; decide +kernel
      have hl : raw13945step1Labels = labelEmbedding1 ∘ raw13945step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13945step1 raw13945step1Labels raw13945step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw13946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13946step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13946step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13946step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13946step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13946 raw13946Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw13946 raw13946Labels = mixedMoment B raw13946step0 raw13946step0Labels := by
      have hz : ∀ j, raw13946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13946step0 = (fun i j => raw13946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13946step0 raw13946; decide +kernel
      have hl : raw13946step0Labels = raw13946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13946 raw13946Labels permutation346 hz
    mixedMoment B raw13946step0 raw13946step0Labels = mixedMoment B raw13946step1 raw13946step1Labels := by
      have ha : raw13946step1 = (fun i j => raw13946step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13946step1 raw13946step0; decide +kernel
      have hl : raw13946step1Labels = raw13946step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13946step0 raw13946step0Labels permutation51 permutation7
    mixedMoment B raw13946step1 raw13946step1Labels = mixedMoment B raw13946step2 raw13946step2Labels := by
      have ha : raw13946step2 = -raw13946step1 := by apply Matrix.ext; change ∀ i j, raw13946step2 i j = -(raw13946step1 i j); unfold raw13946step2 raw13946step1; decide +kernel
      have hl : raw13946step2Labels = raw13946step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13946step2 raw13946step2Labels = mixedMoment B raw13946step3 raw13946step3Labels := by
      have ha : raw13946step3 = raw13946step2 := by apply Matrix.ext; unfold raw13946step3 raw13946step2; decide +kernel
      have hl : raw13946step2Labels = labelEmbedding1 ∘ raw13946step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13946step2 raw13946step2Labels raw13946step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw13947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13947step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13947step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13947 raw13947Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw13947 raw13947Labels = mixedMoment B raw13947step0 raw13947step0Labels := by
      have hz : ∀ j, raw13947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13947step0 = (fun i j => raw13947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13947step0 raw13947; decide +kernel
      have hl : raw13947step0Labels = raw13947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13947 raw13947Labels permutation346 hz
    mixedMoment B raw13947step0 raw13947step0Labels = mixedMoment B raw13947step1 raw13947step1Labels := by
      have ha : raw13947step1 = (fun i j => raw13947step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13947step1 raw13947step0; decide +kernel
      have hl : raw13947step1Labels = raw13947step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13947step0 raw13947step0Labels permutation51 permutation7
    mixedMoment B raw13947step1 raw13947step1Labels = mixedMoment B raw13947step2 raw13947step2Labels := by
      have ha : raw13947step2 = -raw13947step1 := by apply Matrix.ext; change ∀ i j, raw13947step2 i j = -(raw13947step1 i j); unfold raw13947step2 raw13947step1; decide +kernel
      have hl : raw13947step2Labels = raw13947step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13947step2 raw13947step2Labels = mixedMoment B raw13947step3 raw13947step3Labels := by
      have ha : raw13947step3 = raw13947step2 := by apply Matrix.ext; unfold raw13947step3 raw13947step2; decide +kernel
      have hl : raw13947step2Labels = labelEmbedding1 ∘ raw13947step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13947step2 raw13947step2Labels raw13947step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw13948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13948step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13948step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13948step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13948 raw13948Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw13948 raw13948Labels = mixedMoment B raw13948step0 raw13948step0Labels := by
      have hz : ∀ j, raw13948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13948step0 = (fun i j => raw13948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13948step0 raw13948; decide +kernel
      have hl : raw13948step0Labels = raw13948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13948 raw13948Labels permutation346 hz
    mixedMoment B raw13948step0 raw13948step0Labels = mixedMoment B raw13948step1 raw13948step1Labels := by
      have ha : raw13948step1 = (fun i j => raw13948step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13948step1 raw13948step0; decide +kernel
      have hl : raw13948step1Labels = raw13948step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13948step0 raw13948step0Labels permutation51 permutation7
    mixedMoment B raw13948step1 raw13948step1Labels = mixedMoment B raw13948step2 raw13948step2Labels := by
      have ha : raw13948step2 = -raw13948step1 := by apply Matrix.ext; change ∀ i j, raw13948step2 i j = -(raw13948step1 i j); unfold raw13948step2 raw13948step1; decide +kernel
      have hl : raw13948step2Labels = raw13948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13948step2 raw13948step2Labels = mixedMoment B raw13948step3 raw13948step3Labels := by
      have ha : raw13948step3 = raw13948step2 := by apply Matrix.ext; unfold raw13948step3 raw13948step2; decide +kernel
      have hl : raw13948step2Labels = labelEmbedding1 ∘ raw13948step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13948step2 raw13948step2Labels raw13948step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw13949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13949step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13949step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13949step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13949step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13949 raw13949Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw13949 raw13949Labels = mixedMoment B raw13949step0 raw13949step0Labels := by
      have hz : ∀ j, raw13949 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13949step0 = (fun i j => raw13949 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13949step0 raw13949; decide +kernel
      have hl : raw13949step0Labels = raw13949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13949 raw13949Labels permutation265 hz
    mixedMoment B raw13949step0 raw13949step0Labels = mixedMoment B raw13949step1 raw13949step1Labels := by
      have ha : raw13949step1 = (fun i j => raw13949step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13949step1 raw13949step0; decide +kernel
      have hl : raw13949step1Labels = raw13949step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13949step0 raw13949step0Labels permutation40 permutation5
    mixedMoment B raw13949step1 raw13949step1Labels = mixedMoment B raw13949step2 raw13949step2Labels := by
      have ha : raw13949step2 = -raw13949step1 := by apply Matrix.ext; change ∀ i j, raw13949step2 i j = -(raw13949step1 i j); unfold raw13949step2 raw13949step1; decide +kernel
      have hl : raw13949step2Labels = raw13949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13949step2 raw13949step2Labels = mixedMoment B raw13949step3 raw13949step3Labels := by
      have ha : raw13949step3 = raw13949step2 := by apply Matrix.ext; unfold raw13949step3 raw13949step2; decide +kernel
      have hl : raw13949step2Labels = labelEmbedding1 ∘ raw13949step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13949step2 raw13949step2Labels raw13949step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

def raw13950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13950 raw13950Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw13950 raw13950Labels = mixedMoment B raw13950step0 raw13950step0Labels := by
      have ha : raw13950step0 = (fun i j => raw13950 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13950step0 raw13950; decide +kernel
      have hl : raw13950step0Labels = raw13950Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13950 raw13950Labels permutation247 permutation7
    mixedMoment B raw13950step0 raw13950step0Labels = mixedMoment B raw13950step1 raw13950step1Labels := by
      have ha : raw13950step1 = -raw13950step0 := by apply Matrix.ext; change ∀ i j, raw13950step1 i j = -(raw13950step0 i j); unfold raw13950step1 raw13950step0; decide +kernel
      have hl : raw13950step1Labels = raw13950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13950step1 raw13950step1Labels = mixedMoment B raw13950step2 raw13950step2Labels := by
      have ha : raw13950step2 = raw13950step1 := by apply Matrix.ext; unfold raw13950step2 raw13950step1; decide +kernel
      have hl : raw13950step1Labels = labelEmbedding1 ∘ raw13950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13950step1 raw13950step1Labels raw13950step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw13951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13951step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13951step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13951step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13951step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13951step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13951 raw13951Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw13951 raw13951Labels = mixedMoment B raw13951step0 raw13951step0Labels := by
      have hz : ∀ j, raw13951 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13951step0 = (fun i j => raw13951 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13951step0 raw13951; decide +kernel
      have hl : raw13951step0Labels = raw13951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13951 raw13951Labels permutation265 hz
    mixedMoment B raw13951step0 raw13951step0Labels = mixedMoment B raw13951step1 raw13951step1Labels := by
      have ha : raw13951step1 = (fun i j => raw13951step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13951step1 raw13951step0; decide +kernel
      have hl : raw13951step1Labels = raw13951step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13951step0 raw13951step0Labels permutation51 permutation7
    mixedMoment B raw13951step1 raw13951step1Labels = mixedMoment B raw13951step2 raw13951step2Labels := by
      have ha : raw13951step2 = -raw13951step1 := by apply Matrix.ext; change ∀ i j, raw13951step2 i j = -(raw13951step1 i j); unfold raw13951step2 raw13951step1; decide +kernel
      have hl : raw13951step2Labels = raw13951step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13951step2 raw13951step2Labels = mixedMoment B raw13951step3 raw13951step3Labels := by
      have ha : raw13951step3 = raw13951step2 := by apply Matrix.ext; unfold raw13951step3 raw13951step2; decide +kernel
      have hl : raw13951step2Labels = labelEmbedding1 ∘ raw13951step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13951step2 raw13951step2Labels raw13951step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
