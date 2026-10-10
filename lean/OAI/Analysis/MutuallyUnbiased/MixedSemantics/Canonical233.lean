import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29824 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29824step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29824 raw29824Labels = mixedMoment B node5063 node5063Labels := by
  calc
    mixedMoment B raw29824 raw29824Labels = mixedMoment B raw29824step0 raw29824step0Labels := by
      have hz : ∀ j, raw29824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29824step0 = (fun i j => raw29824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29824step0 raw29824; decide +kernel
      have hl : raw29824step0Labels = raw29824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29824 raw29824Labels permutation346 hz
    mixedMoment B raw29824step0 raw29824step0Labels = mixedMoment B raw29824step1 raw29824step1Labels := by
      have ha : raw29824step1 = (fun i j => raw29824step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29824step1 raw29824step0; decide +kernel
      have hl : raw29824step1Labels = raw29824step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29824step0 raw29824step0Labels permutation32 permutation7
    mixedMoment B raw29824step1 raw29824step1Labels = mixedMoment B raw29824step2 raw29824step2Labels := by
      have ha : raw29824step2 = raw29824step1 := by apply Matrix.ext; unfold raw29824step2 raw29824step1; decide +kernel
      have hl : raw29824step1Labels = labelEmbedding10 ∘ raw29824step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29824step1 raw29824step1Labels raw29824step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5063 node5063Labels := by rfl

def raw29825 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29825step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29825 raw29825Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw29825 raw29825Labels = mixedMoment B raw29825step0 raw29825step0Labels := by
      have hz : ∀ j, raw29825 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29825step0 = (fun i j => raw29825 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29825step0 raw29825; decide +kernel
      have hl : raw29825step0Labels = raw29825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29825 raw29825Labels permutation346 hz
    mixedMoment B raw29825step0 raw29825step0Labels = mixedMoment B raw29825step1 raw29825step1Labels := by
      have ha : raw29825step1 = (fun i j => raw29825step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29825step1 raw29825step0; decide +kernel
      have hl : raw29825step1Labels = raw29825step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29825step0 raw29825step0Labels permutation32 permutation6
    mixedMoment B raw29825step1 raw29825step1Labels = mixedMoment B raw29825step2 raw29825step2Labels := by
      have ha : raw29825step2 = raw29825step1 := by apply Matrix.ext; unfold raw29825step2 raw29825step1; decide +kernel
      have hl : raw29825step1Labels = labelEmbedding9 ∘ raw29825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29825step1 raw29825step1Labels raw29825step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw29826 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29826step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29826step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29826 raw29826Labels = mixedMoment B node5182 node5182Labels := by
  calc
    mixedMoment B raw29826 raw29826Labels = mixedMoment B raw29826step0 raw29826step0Labels := by
      have ha : raw29826step0 = (fun i j => raw29826 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29826step0 raw29826; decide +kernel
      have hl : raw29826step0Labels = raw29826Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29826 raw29826Labels permutation152 permutation6
    mixedMoment B raw29826step0 raw29826step0Labels = mixedMoment B raw29826step1 raw29826step1Labels := by
      have ha : raw29826step1 = raw29826step0 := by apply Matrix.ext; unfold raw29826step1 raw29826step0; decide +kernel
      have hl : raw29826step0Labels = labelEmbedding9 ∘ raw29826step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29826step0 raw29826step0Labels raw29826step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5182 node5182Labels := by rfl

def raw29827 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw29827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29827 raw29827Labels = mixedMoment B node5016 node5016Labels := by
  calc
    mixedMoment B raw29827 raw29827Labels = mixedMoment B raw29827step0 raw29827step0Labels := by
      have hz : ∀ j, raw29827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29827step0 = (fun i j => raw29827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29827step0 raw29827; decide +kernel
      have hl : raw29827step0Labels = raw29827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29827 raw29827Labels permutation346 hz
    mixedMoment B raw29827step0 raw29827step0Labels = mixedMoment B raw29827step1 raw29827step1Labels := by
      have ha : raw29827step1 = (fun i j => raw29827step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29827step1 raw29827step0; decide +kernel
      have hl : raw29827step1Labels = raw29827step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29827step0 raw29827step0Labels permutation126 permutation2
    _ = mixedMoment B node5016 node5016Labels := by rfl

def raw29828 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw29828step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw29828step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29828 raw29828Labels = mixedMoment B node5193 node5193Labels := by
  calc
    mixedMoment B raw29828 raw29828Labels = mixedMoment B raw29828step0 raw29828step0Labels := by
      have hz : ∀ j, raw29828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29828step0 = (fun i j => raw29828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29828step0 raw29828; decide +kernel
      have hl : raw29828step0Labels = raw29828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29828 raw29828Labels permutation346 hz
    mixedMoment B raw29828step0 raw29828step0Labels = mixedMoment B raw29828step1 raw29828step1Labels := by
      have ha : raw29828step1 = (fun i j => raw29828step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29828step1 raw29828step0; decide +kernel
      have hl : raw29828step1Labels = raw29828step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29828step0 raw29828step0Labels permutation32 permutation6
    mixedMoment B raw29828step1 raw29828step1Labels = mixedMoment B raw29828step2 raw29828step2Labels := by
      have ha : raw29828step2 = raw29828step1 := by apply Matrix.ext; unfold raw29828step2 raw29828step1; decide +kernel
      have hl : raw29828step1Labels = labelEmbedding9 ∘ raw29828step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29828step1 raw29828step1Labels raw29828step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5193 node5193Labels := by rfl

def raw29829 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29829step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29829 raw29829Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw29829 raw29829Labels = mixedMoment B raw29829step0 raw29829step0Labels := by
      have ha : raw29829step0 = (fun i j => raw29829 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29829step0 raw29829; decide +kernel
      have hl : raw29829step0Labels = raw29829Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29829 raw29829Labels permutation152 permutation6
    mixedMoment B raw29829step0 raw29829step0Labels = mixedMoment B raw29829step1 raw29829step1Labels := by
      have ha : raw29829step1 = raw29829step0 := by apply Matrix.ext; unfold raw29829step1 raw29829step0; decide +kernel
      have hl : raw29829step0Labels = labelEmbedding9 ∘ raw29829step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29829step0 raw29829step0Labels raw29829step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw29830 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29830step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29830 raw29830Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw29830 raw29830Labels = mixedMoment B raw29830step0 raw29830step0Labels := by
      have ha : raw29830step0 = (fun i j => raw29830 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29830step0 raw29830; decide +kernel
      have hl : raw29830step0Labels = raw29830Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29830 raw29830Labels permutation152 permutation6
    mixedMoment B raw29830step0 raw29830step0Labels = mixedMoment B raw29830step1 raw29830step1Labels := by
      have ha : raw29830step1 = raw29830step0 := by apply Matrix.ext; unfold raw29830step1 raw29830step0; decide +kernel
      have hl : raw29830step0Labels = labelEmbedding9 ∘ raw29830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29830step0 raw29830step0Labels raw29830step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw29831 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29831 raw29831Labels = mixedMoment B node5011 node5011Labels := by
  calc
    mixedMoment B raw29831 raw29831Labels = mixedMoment B raw29831step0 raw29831step0Labels := by
      have ha : raw29831step0 = (fun i j => raw29831 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29831step0 raw29831; decide +kernel
      have hl : raw29831step0Labels = raw29831Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29831 raw29831Labels permutation584 permutation2
    _ = mixedMoment B node5011 node5011Labels := by rfl

def raw29832 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw29832step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw29832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29832 raw29832Labels = mixedMoment B node5142 node5142Labels := by
  calc
    mixedMoment B raw29832 raw29832Labels = mixedMoment B raw29832step0 raw29832step0Labels := by
      have ha : raw29832step0 = (fun i j => raw29832 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29832step0 raw29832; decide +kernel
      have hl : raw29832step0Labels = raw29832Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29832 raw29832Labels permutation152 permutation6
    mixedMoment B raw29832step0 raw29832step0Labels = mixedMoment B raw29832step1 raw29832step1Labels := by
      have ha : raw29832step1 = raw29832step0 := by apply Matrix.ext; unfold raw29832step1 raw29832step0; decide +kernel
      have hl : raw29832step0Labels = labelEmbedding9 ∘ raw29832step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29832step0 raw29832step0Labels raw29832step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5142 node5142Labels := by rfl

def raw29833 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29833step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29833 raw29833Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw29833 raw29833Labels = mixedMoment B raw29833step0 raw29833step0Labels := by
      have hz : ∀ j, raw29833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29833step0 = (fun i j => raw29833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29833step0 raw29833; decide +kernel
      have hl : raw29833step0Labels = raw29833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29833 raw29833Labels permutation346 hz
    mixedMoment B raw29833step0 raw29833step0Labels = mixedMoment B raw29833step1 raw29833step1Labels := by
      have ha : raw29833step1 = (fun i j => raw29833step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29833step1 raw29833step0; decide +kernel
      have hl : raw29833step1Labels = raw29833step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29833step0 raw29833step0Labels permutation32 permutation6
    mixedMoment B raw29833step1 raw29833step1Labels = mixedMoment B raw29833step2 raw29833step2Labels := by
      have ha : raw29833step2 = raw29833step1 := by apply Matrix.ext; unfold raw29833step2 raw29833step1; decide +kernel
      have hl : raw29833step1Labels = labelEmbedding9 ∘ raw29833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29833step1 raw29833step1Labels raw29833step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw29834 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29834step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29834 raw29834Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw29834 raw29834Labels = mixedMoment B raw29834step0 raw29834step0Labels := by
      have hz : ∀ j, raw29834 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29834step0 = (fun i j => raw29834 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29834step0 raw29834; decide +kernel
      have hl : raw29834step0Labels = raw29834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29834 raw29834Labels permutation346 hz
    mixedMoment B raw29834step0 raw29834step0Labels = mixedMoment B raw29834step1 raw29834step1Labels := by
      have ha : raw29834step1 = (fun i j => raw29834step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29834step1 raw29834step0; decide +kernel
      have hl : raw29834step1Labels = raw29834step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29834step0 raw29834step0Labels permutation32 permutation6
    mixedMoment B raw29834step1 raw29834step1Labels = mixedMoment B raw29834step2 raw29834step2Labels := by
      have ha : raw29834step2 = raw29834step1 := by apply Matrix.ext; unfold raw29834step2 raw29834step1; decide +kernel
      have hl : raw29834step1Labels = labelEmbedding9 ∘ raw29834step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29834step1 raw29834step1Labels raw29834step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw29835 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29835step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29835 raw29835Labels = mixedMoment B node5131 node5131Labels := by
  calc
    mixedMoment B raw29835 raw29835Labels = mixedMoment B raw29835step0 raw29835step0Labels := by
      have ha : raw29835step0 = (fun i j => raw29835 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29835step0 raw29835; decide +kernel
      have hl : raw29835step0Labels = raw29835Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29835 raw29835Labels permutation152 permutation6
    mixedMoment B raw29835step0 raw29835step0Labels = mixedMoment B raw29835step1 raw29835step1Labels := by
      have ha : raw29835step1 = raw29835step0 := by apply Matrix.ext; unfold raw29835step1 raw29835step0; decide +kernel
      have hl : raw29835step0Labels = labelEmbedding9 ∘ raw29835step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29835step0 raw29835step0Labels raw29835step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5131 node5131Labels := by rfl

def raw29836 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw29836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29836 raw29836Labels = mixedMoment B node5019 node5019Labels := by
  calc
    mixedMoment B raw29836 raw29836Labels = mixedMoment B raw29836step0 raw29836step0Labels := by
      have hz : ∀ j, raw29836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29836step0 = (fun i j => raw29836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29836step0 raw29836; decide +kernel
      have hl : raw29836step0Labels = raw29836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29836 raw29836Labels permutation346 hz
    mixedMoment B raw29836step0 raw29836step0Labels = mixedMoment B raw29836step1 raw29836step1Labels := by
      have ha : raw29836step1 = (fun i j => raw29836step0 (permutation124 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29836step1 raw29836step0; decide +kernel
      have hl : raw29836step1Labels = raw29836step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29836step0 raw29836step0Labels permutation124 permutation2
    _ = mixedMoment B node5019 node5019Labels := by rfl

def raw29837 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw29837step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw29837step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29837 raw29837Labels = mixedMoment B node5156 node5156Labels := by
  calc
    mixedMoment B raw29837 raw29837Labels = mixedMoment B raw29837step0 raw29837step0Labels := by
      have hz : ∀ j, raw29837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29837step0 = (fun i j => raw29837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29837step0 raw29837; decide +kernel
      have hl : raw29837step0Labels = raw29837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29837 raw29837Labels permutation346 hz
    mixedMoment B raw29837step0 raw29837step0Labels = mixedMoment B raw29837step1 raw29837step1Labels := by
      have ha : raw29837step1 = (fun i j => raw29837step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29837step1 raw29837step0; decide +kernel
      have hl : raw29837step1Labels = raw29837step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29837step0 raw29837step0Labels permutation32 permutation6
    mixedMoment B raw29837step1 raw29837step1Labels = mixedMoment B raw29837step2 raw29837step2Labels := by
      have ha : raw29837step2 = raw29837step1 := by apply Matrix.ext; unfold raw29837step2 raw29837step1; decide +kernel
      have hl : raw29837step1Labels = labelEmbedding9 ∘ raw29837step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29837step1 raw29837step1Labels raw29837step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5156 node5156Labels := by rfl

def raw29838 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29838step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29838 raw29838Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw29838 raw29838Labels = mixedMoment B raw29838step0 raw29838step0Labels := by
      have hz : ∀ j, raw29838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29838step0 = (fun i j => raw29838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29838step0 raw29838; decide +kernel
      have hl : raw29838step0Labels = raw29838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29838 raw29838Labels permutation346 hz
    mixedMoment B raw29838step0 raw29838step0Labels = mixedMoment B raw29838step1 raw29838step1Labels := by
      have ha : raw29838step1 = (fun i j => raw29838step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29838step1 raw29838step0; decide +kernel
      have hl : raw29838step1Labels = raw29838step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29838step0 raw29838step0Labels permutation33 permutation7
    mixedMoment B raw29838step1 raw29838step1Labels = mixedMoment B raw29838step2 raw29838step2Labels := by
      have ha : raw29838step2 = raw29838step1 := by apply Matrix.ext; unfold raw29838step2 raw29838step1; decide +kernel
      have hl : raw29838step1Labels = labelEmbedding1 ∘ raw29838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29838step1 raw29838step1Labels raw29838step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw29839 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29839step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29839 raw29839Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw29839 raw29839Labels = mixedMoment B raw29839step0 raw29839step0Labels := by
      have ha : raw29839step0 = (fun i j => raw29839 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29839step0 raw29839; decide +kernel
      have hl : raw29839step0Labels = raw29839Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29839 raw29839Labels permutation159 permutation7
    mixedMoment B raw29839step0 raw29839step0Labels = mixedMoment B raw29839step1 raw29839step1Labels := by
      have ha : raw29839step1 = raw29839step0 := by apply Matrix.ext; unfold raw29839step1 raw29839step0; decide +kernel
      have hl : raw29839step0Labels = labelEmbedding1 ∘ raw29839step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29839step0 raw29839step0Labels raw29839step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw29840 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29840step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29840step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29840 raw29840Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw29840 raw29840Labels = mixedMoment B raw29840step0 raw29840step0Labels := by
      have hz : ∀ j, raw29840 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29840step0 = (fun i j => raw29840 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29840step0 raw29840; decide +kernel
      have hl : raw29840step0Labels = raw29840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29840 raw29840Labels permutation346 hz
    mixedMoment B raw29840step0 raw29840step0Labels = mixedMoment B raw29840step1 raw29840step1Labels := by
      have ha : raw29840step1 = (fun i j => raw29840step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29840step1 raw29840step0; decide +kernel
      have hl : raw29840step1Labels = raw29840step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29840step0 raw29840step0Labels permutation33 permutation7
    mixedMoment B raw29840step1 raw29840step1Labels = mixedMoment B raw29840step2 raw29840step2Labels := by
      have ha : raw29840step2 = raw29840step1 := by apply Matrix.ext; unfold raw29840step2 raw29840step1; decide +kernel
      have hl : raw29840step1Labels = labelEmbedding1 ∘ raw29840step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29840step1 raw29840step1Labels raw29840step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw29841 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29841Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29841step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29841step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29841 raw29841Labels = mixedMoment B node2468 node2468Labels := by
  calc
    mixedMoment B raw29841 raw29841Labels = mixedMoment B raw29841step0 raw29841step0Labels := by
      have hz : ∀ j, raw29841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29841step0 = (fun i j => raw29841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29841step0 raw29841; decide +kernel
      have hl : raw29841step0Labels = raw29841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29841 raw29841Labels permutation346 hz
    mixedMoment B raw29841step0 raw29841step0Labels = mixedMoment B raw29841step1 raw29841step1Labels := by
      have ha : raw29841step1 = (fun i j => raw29841step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29841step1 raw29841step0; decide +kernel
      have hl : raw29841step1Labels = raw29841step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29841step0 raw29841step0Labels permutation32 permutation7
    mixedMoment B raw29841step1 raw29841step1Labels = mixedMoment B raw29841step2 raw29841step2Labels := by
      have ha : raw29841step2 = raw29841step1 := by apply Matrix.ext; unfold raw29841step2 raw29841step1; decide +kernel
      have hl : raw29841step1Labels = labelEmbedding1 ∘ raw29841step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29841step1 raw29841step1Labels raw29841step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2468 node2468Labels := by rfl

def raw29842 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29842Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29842step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29842 raw29842Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw29842 raw29842Labels = mixedMoment B raw29842step0 raw29842step0Labels := by
      have hz : ∀ j, raw29842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29842step0 = (fun i j => raw29842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29842step0 raw29842; decide +kernel
      have hl : raw29842step0Labels = raw29842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29842 raw29842Labels permutation346 hz
    mixedMoment B raw29842step0 raw29842step0Labels = mixedMoment B raw29842step1 raw29842step1Labels := by
      have ha : raw29842step1 = (fun i j => raw29842step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29842step1 raw29842step0; decide +kernel
      have hl : raw29842step1Labels = raw29842step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29842step0 raw29842step0Labels permutation33 permutation7
    mixedMoment B raw29842step1 raw29842step1Labels = mixedMoment B raw29842step2 raw29842step2Labels := by
      have ha : raw29842step2 = raw29842step1 := by apply Matrix.ext; unfold raw29842step2 raw29842step1; decide +kernel
      have hl : raw29842step1Labels = labelEmbedding1 ∘ raw29842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29842step1 raw29842step1Labels raw29842step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3174 node3174Labels := by rfl

def raw29843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29843Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29843step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29843 raw29843Labels = mixedMoment B node2850 node2850Labels := by
  calc
    mixedMoment B raw29843 raw29843Labels = mixedMoment B raw29843step0 raw29843step0Labels := by
      have ha : raw29843step0 = (fun i j => raw29843 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29843step0 raw29843; decide +kernel
      have hl : raw29843step0Labels = raw29843Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29843 raw29843Labels permutation159 permutation7
    mixedMoment B raw29843step0 raw29843step0Labels = mixedMoment B raw29843step1 raw29843step1Labels := by
      have ha : raw29843step1 = raw29843step0 := by apply Matrix.ext; unfold raw29843step1 raw29843step0; decide +kernel
      have hl : raw29843step0Labels = labelEmbedding1 ∘ raw29843step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29843step0 raw29843step0Labels raw29843step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2850 node2850Labels := by rfl

def raw29844 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29844Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29844step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29844step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29844 raw29844Labels = mixedMoment B node2855 node2855Labels := by
  calc
    mixedMoment B raw29844 raw29844Labels = mixedMoment B raw29844step0 raw29844step0Labels := by
      have hz : ∀ j, raw29844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29844step0 = (fun i j => raw29844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29844step0 raw29844; decide +kernel
      have hl : raw29844step0Labels = raw29844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29844 raw29844Labels permutation346 hz
    mixedMoment B raw29844step0 raw29844step0Labels = mixedMoment B raw29844step1 raw29844step1Labels := by
      have ha : raw29844step1 = (fun i j => raw29844step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29844step1 raw29844step0; decide +kernel
      have hl : raw29844step1Labels = raw29844step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29844step0 raw29844step0Labels permutation33 permutation7
    mixedMoment B raw29844step1 raw29844step1Labels = mixedMoment B raw29844step2 raw29844step2Labels := by
      have ha : raw29844step2 = raw29844step1 := by apply Matrix.ext; unfold raw29844step2 raw29844step1; decide +kernel
      have hl : raw29844step1Labels = labelEmbedding1 ∘ raw29844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29844step1 raw29844step1Labels raw29844step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2855 node2855Labels := by rfl

def raw29845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29845Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29845step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29845 raw29845Labels = mixedMoment B node2856 node2856Labels := by
  calc
    mixedMoment B raw29845 raw29845Labels = mixedMoment B raw29845step0 raw29845step0Labels := by
      have hz : ∀ j, raw29845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29845step0 = (fun i j => raw29845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29845step0 raw29845; decide +kernel
      have hl : raw29845step0Labels = raw29845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29845 raw29845Labels permutation346 hz
    mixedMoment B raw29845step0 raw29845step0Labels = mixedMoment B raw29845step1 raw29845step1Labels := by
      have ha : raw29845step1 = (fun i j => raw29845step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29845step1 raw29845step0; decide +kernel
      have hl : raw29845step1Labels = raw29845step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29845step0 raw29845step0Labels permutation32 permutation7
    mixedMoment B raw29845step1 raw29845step1Labels = mixedMoment B raw29845step2 raw29845step2Labels := by
      have ha : raw29845step2 = raw29845step1 := by apply Matrix.ext; unfold raw29845step2 raw29845step1; decide +kernel
      have hl : raw29845step1Labels = labelEmbedding1 ∘ raw29845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29845step1 raw29845step1Labels raw29845step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2856 node2856Labels := by rfl

def raw29846 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29846Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29846step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29846 raw29846Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw29846 raw29846Labels = mixedMoment B raw29846step0 raw29846step0Labels := by
      have ha : raw29846step0 = (fun i j => raw29846 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29846step0 raw29846; decide +kernel
      have hl : raw29846step0Labels = raw29846Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29846 raw29846Labels permutation153 permutation7
    mixedMoment B raw29846step0 raw29846step0Labels = mixedMoment B raw29846step1 raw29846step1Labels := by
      have ha : raw29846step1 = raw29846step0 := by apply Matrix.ext; unfold raw29846step1 raw29846step0; decide +kernel
      have hl : raw29846step0Labels = labelEmbedding1 ∘ raw29846step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29846step0 raw29846step0Labels raw29846step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3199 node3199Labels := by rfl

def raw29847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29847Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29847step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29847 raw29847Labels = mixedMoment B node2981 node2981Labels := by
  calc
    mixedMoment B raw29847 raw29847Labels = mixedMoment B raw29847step0 raw29847step0Labels := by
      have ha : raw29847step0 = (fun i j => raw29847 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29847step0 raw29847; decide +kernel
      have hl : raw29847step0Labels = raw29847Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29847 raw29847Labels permutation153 permutation7
    mixedMoment B raw29847step0 raw29847step0Labels = mixedMoment B raw29847step1 raw29847step1Labels := by
      have ha : raw29847step1 = raw29847step0 := by apply Matrix.ext; unfold raw29847step1 raw29847step0; decide +kernel
      have hl : raw29847step0Labels = labelEmbedding1 ∘ raw29847step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29847step0 raw29847step0Labels raw29847step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2981 node2981Labels := by rfl

def raw29848 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29848Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29848 raw29848Labels = mixedMoment B node2912 node2912Labels := by
  calc
    mixedMoment B raw29848 raw29848Labels = mixedMoment B raw29848step0 raw29848step0Labels := by
      have ha : raw29848step0 = (fun i j => raw29848 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29848step0 raw29848; decide +kernel
      have hl : raw29848step0Labels = raw29848Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29848 raw29848Labels permutation153 permutation7
    mixedMoment B raw29848step0 raw29848step0Labels = mixedMoment B raw29848step1 raw29848step1Labels := by
      have ha : raw29848step1 = raw29848step0 := by apply Matrix.ext; unfold raw29848step1 raw29848step0; decide +kernel
      have hl : raw29848step0Labels = labelEmbedding1 ∘ raw29848step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29848step0 raw29848step0Labels raw29848step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2912 node2912Labels := by rfl

def raw29849 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29849Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29849step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29849 raw29849Labels = mixedMoment B node2913 node2913Labels := by
  calc
    mixedMoment B raw29849 raw29849Labels = mixedMoment B raw29849step0 raw29849step0Labels := by
      have ha : raw29849step0 = (fun i j => raw29849 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29849step0 raw29849; decide +kernel
      have hl : raw29849step0Labels = raw29849Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29849 raw29849Labels permutation152 permutation7
    mixedMoment B raw29849step0 raw29849step0Labels = mixedMoment B raw29849step1 raw29849step1Labels := by
      have ha : raw29849step1 = raw29849step0 := by apply Matrix.ext; unfold raw29849step1 raw29849step0; decide +kernel
      have hl : raw29849step0Labels = labelEmbedding1 ∘ raw29849step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29849step0 raw29849step0Labels raw29849step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2913 node2913Labels := by rfl

def raw29850 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29850Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29850step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw29850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw29850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29850 raw29850Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw29850 raw29850Labels = mixedMoment B raw29850step0 raw29850step0Labels := by
      have hz : ∀ j, raw29850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29850step0 = (fun i j => raw29850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29850step0 raw29850; decide +kernel
      have hl : raw29850step0Labels = raw29850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29850 raw29850Labels permutation346 hz
    mixedMoment B raw29850step0 raw29850step0Labels = mixedMoment B raw29850step1 raw29850step1Labels := by
      have ha : raw29850step1 = (fun i j => raw29850step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29850step1 raw29850step0; decide +kernel
      have hl : raw29850step1Labels = raw29850step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29850step0 raw29850step0Labels permutation33 permutation7
    mixedMoment B raw29850step1 raw29850step1Labels = mixedMoment B raw29850step2 raw29850step2Labels := by
      have ha : raw29850step2 = raw29850step1 := by apply Matrix.ext; unfold raw29850step2 raw29850step1; decide +kernel
      have hl : raw29850step1Labels = labelEmbedding1 ∘ raw29850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29850step1 raw29850step1Labels raw29850step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3198 node3198Labels := by rfl

def raw29851 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29851Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29851step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw29851step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw29851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29851 raw29851Labels = mixedMoment B node2979 node2979Labels := by
  calc
    mixedMoment B raw29851 raw29851Labels = mixedMoment B raw29851step0 raw29851step0Labels := by
      have hz : ∀ j, raw29851 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29851step0 = (fun i j => raw29851 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29851step0 raw29851; decide +kernel
      have hl : raw29851step0Labels = raw29851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29851 raw29851Labels permutation346 hz
    mixedMoment B raw29851step0 raw29851step0Labels = mixedMoment B raw29851step1 raw29851step1Labels := by
      have ha : raw29851step1 = (fun i j => raw29851step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29851step1 raw29851step0; decide +kernel
      have hl : raw29851step1Labels = raw29851step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29851step0 raw29851step0Labels permutation33 permutation7
    mixedMoment B raw29851step1 raw29851step1Labels = mixedMoment B raw29851step2 raw29851step2Labels := by
      have ha : raw29851step2 = raw29851step1 := by apply Matrix.ext; unfold raw29851step2 raw29851step1; decide +kernel
      have hl : raw29851step1Labels = labelEmbedding1 ∘ raw29851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29851step1 raw29851step1Labels raw29851step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2979 node2979Labels := by rfl

def raw29852 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29852step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29852 raw29852Labels = mixedMoment B node2905 node2905Labels := by
  calc
    mixedMoment B raw29852 raw29852Labels = mixedMoment B raw29852step0 raw29852step0Labels := by
      have ha : raw29852step0 = (fun i j => raw29852 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29852step0 raw29852; decide +kernel
      have hl : raw29852step0Labels = raw29852Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29852 raw29852Labels permutation159 permutation7
    mixedMoment B raw29852step0 raw29852step0Labels = mixedMoment B raw29852step1 raw29852step1Labels := by
      have ha : raw29852step1 = raw29852step0 := by apply Matrix.ext; unfold raw29852step1 raw29852step0; decide +kernel
      have hl : raw29852step0Labels = labelEmbedding1 ∘ raw29852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29852step0 raw29852step0Labels raw29852step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2905 node2905Labels := by rfl

def raw29853 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29853step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw29853step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw29853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29853 raw29853Labels = mixedMoment B node2910 node2910Labels := by
  calc
    mixedMoment B raw29853 raw29853Labels = mixedMoment B raw29853step0 raw29853step0Labels := by
      have hz : ∀ j, raw29853 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29853step0 = (fun i j => raw29853 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29853step0 raw29853; decide +kernel
      have hl : raw29853step0Labels = raw29853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29853 raw29853Labels permutation346 hz
    mixedMoment B raw29853step0 raw29853step0Labels = mixedMoment B raw29853step1 raw29853step1Labels := by
      have ha : raw29853step1 = (fun i j => raw29853step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29853step1 raw29853step0; decide +kernel
      have hl : raw29853step1Labels = raw29853step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29853step0 raw29853step0Labels permutation33 permutation7
    mixedMoment B raw29853step1 raw29853step1Labels = mixedMoment B raw29853step2 raw29853step2Labels := by
      have ha : raw29853step2 = raw29853step1 := by apply Matrix.ext; unfold raw29853step2 raw29853step1; decide +kernel
      have hl : raw29853step1Labels = labelEmbedding1 ∘ raw29853step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29853step1 raw29853step1Labels raw29853step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2910 node2910Labels := by rfl

def raw29854 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29854step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29854 raw29854Labels = mixedMoment B node2911 node2911Labels := by
  calc
    mixedMoment B raw29854 raw29854Labels = mixedMoment B raw29854step0 raw29854step0Labels := by
      have hz : ∀ j, raw29854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29854step0 = (fun i j => raw29854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29854step0 raw29854; decide +kernel
      have hl : raw29854step0Labels = raw29854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29854 raw29854Labels permutation346 hz
    mixedMoment B raw29854step0 raw29854step0Labels = mixedMoment B raw29854step1 raw29854step1Labels := by
      have ha : raw29854step1 = (fun i j => raw29854step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29854step1 raw29854step0; decide +kernel
      have hl : raw29854step1Labels = raw29854step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29854step0 raw29854step0Labels permutation32 permutation7
    mixedMoment B raw29854step1 raw29854step1Labels = mixedMoment B raw29854step2 raw29854step2Labels := by
      have ha : raw29854step2 = raw29854step1 := by apply Matrix.ext; unfold raw29854step2 raw29854step1; decide +kernel
      have hl : raw29854step1Labels = labelEmbedding1 ∘ raw29854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29854step1 raw29854step1Labels raw29854step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2911 node2911Labels := by rfl

def raw29855 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29855step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29855step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29855step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29855step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29855 raw29855Labels = mixedMoment B node3207 node3207Labels := by
  calc
    mixedMoment B raw29855 raw29855Labels = mixedMoment B raw29855step0 raw29855step0Labels := by
      have hz : ∀ j, raw29855 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29855step0 = (fun i j => raw29855 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29855step0 raw29855; decide +kernel
      have hl : raw29855step0Labels = raw29855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29855 raw29855Labels permutation346 hz
    mixedMoment B raw29855step0 raw29855step0Labels = mixedMoment B raw29855step1 raw29855step1Labels := by
      have ha : raw29855step1 = (fun i j => raw29855step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29855step1 raw29855step0; decide +kernel
      have hl : raw29855step1Labels = raw29855step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29855step0 raw29855step0Labels permutation32 permutation7
    mixedMoment B raw29855step1 raw29855step1Labels = mixedMoment B raw29855step2 raw29855step2Labels := by
      have ha : raw29855step2 = raw29855step1 := by apply Matrix.ext; unfold raw29855step2 raw29855step1; decide +kernel
      have hl : raw29855step1Labels = labelEmbedding1 ∘ raw29855step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29855step1 raw29855step1Labels raw29855step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3207 node3207Labels := by rfl

def raw29856 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29856step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29856step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29856 raw29856Labels = mixedMoment B node2991 node2991Labels := by
  calc
    mixedMoment B raw29856 raw29856Labels = mixedMoment B raw29856step0 raw29856step0Labels := by
      have hz : ∀ j, raw29856 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29856step0 = (fun i j => raw29856 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29856step0 raw29856; decide +kernel
      have hl : raw29856step0Labels = raw29856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29856 raw29856Labels permutation346 hz
    mixedMoment B raw29856step0 raw29856step0Labels = mixedMoment B raw29856step1 raw29856step1Labels := by
      have ha : raw29856step1 = (fun i j => raw29856step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29856step1 raw29856step0; decide +kernel
      have hl : raw29856step1Labels = raw29856step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29856step0 raw29856step0Labels permutation32 permutation7
    mixedMoment B raw29856step1 raw29856step1Labels = mixedMoment B raw29856step2 raw29856step2Labels := by
      have ha : raw29856step2 = raw29856step1 := by apply Matrix.ext; unfold raw29856step2 raw29856step1; decide +kernel
      have hl : raw29856step1Labels = labelEmbedding1 ∘ raw29856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29856step1 raw29856step1Labels raw29856step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2991 node2991Labels := by rfl

def raw29857 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29857step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29857 raw29857Labels = mixedMoment B node2917 node2917Labels := by
  calc
    mixedMoment B raw29857 raw29857Labels = mixedMoment B raw29857step0 raw29857step0Labels := by
      have ha : raw29857step0 = (fun i j => raw29857 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29857step0 raw29857; decide +kernel
      have hl : raw29857step0Labels = raw29857Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29857 raw29857Labels permutation158 permutation7
    mixedMoment B raw29857step0 raw29857step0Labels = mixedMoment B raw29857step1 raw29857step1Labels := by
      have ha : raw29857step1 = raw29857step0 := by apply Matrix.ext; unfold raw29857step1 raw29857step0; decide +kernel
      have hl : raw29857step0Labels = labelEmbedding1 ∘ raw29857step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29857step0 raw29857step0Labels raw29857step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2917 node2917Labels := by rfl

def raw29858 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29858step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29858 raw29858Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw29858 raw29858Labels = mixedMoment B raw29858step0 raw29858step0Labels := by
      have hz : ∀ j, raw29858 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29858step0 = (fun i j => raw29858 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29858step0 raw29858; decide +kernel
      have hl : raw29858step0Labels = raw29858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29858 raw29858Labels permutation346 hz
    mixedMoment B raw29858step0 raw29858step0Labels = mixedMoment B raw29858step1 raw29858step1Labels := by
      have ha : raw29858step1 = (fun i j => raw29858step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29858step1 raw29858step0; decide +kernel
      have hl : raw29858step1Labels = raw29858step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29858step0 raw29858step0Labels permutation32 permutation7
    mixedMoment B raw29858step1 raw29858step1Labels = mixedMoment B raw29858step2 raw29858step2Labels := by
      have ha : raw29858step2 = raw29858step1 := by apply Matrix.ext; unfold raw29858step2 raw29858step1; decide +kernel
      have hl : raw29858step1Labels = labelEmbedding1 ∘ raw29858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29858step1 raw29858step1Labels raw29858step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw29859 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29859step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29859step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29859step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29859step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29859 raw29859Labels = mixedMoment B node2968 node2968Labels := by
  calc
    mixedMoment B raw29859 raw29859Labels = mixedMoment B raw29859step0 raw29859step0Labels := by
      have hz : ∀ j, raw29859 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29859step0 = (fun i j => raw29859 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29859step0 raw29859; decide +kernel
      have hl : raw29859step0Labels = raw29859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29859 raw29859Labels permutation434 hz
    mixedMoment B raw29859step0 raw29859step0Labels = mixedMoment B raw29859step1 raw29859step1Labels := by
      have hz : ∀ j, raw29859step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29859step1 = (fun i j => raw29859step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29859step1 raw29859step0; decide +kernel
      have hl : raw29859step1Labels = raw29859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29859step0 raw29859step0Labels permutation80 hz
    mixedMoment B raw29859step1 raw29859step1Labels = mixedMoment B raw29859step2 raw29859step2Labels := by
      have ha : raw29859step2 = (fun i j => raw29859step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29859step2 raw29859step1; decide +kernel
      have hl : raw29859step2Labels = raw29859step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29859step1 raw29859step1Labels permutation9 permutation7
    mixedMoment B raw29859step2 raw29859step2Labels = mixedMoment B raw29859step3 raw29859step3Labels := by
      have ha : raw29859step3 = raw29859step2 := by apply Matrix.ext; unfold raw29859step3 raw29859step2; decide +kernel
      have hl : raw29859step2Labels = labelEmbedding1 ∘ raw29859step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29859step2 raw29859step2Labels raw29859step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2968 node2968Labels := by rfl

def raw29860 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw29860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29860 raw29860Labels = mixedMoment B node3439 node3439Labels := by
  calc
    mixedMoment B raw29860 raw29860Labels = mixedMoment B raw29860step0 raw29860step0Labels := by
      have hz : ∀ j, raw29860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29860step0 = (fun i j => raw29860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29860step0 raw29860; decide +kernel
      have hl : raw29860step0Labels = raw29860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29860 raw29860Labels permutation346 hz
    mixedMoment B raw29860step0 raw29860step0Labels = mixedMoment B raw29860step1 raw29860step1Labels := by
      have ha : raw29860step1 = -raw29860step0 := by apply Matrix.ext; change ∀ i j, raw29860step1 i j = -(raw29860step0 i j); unfold raw29860step1 raw29860step0; decide +kernel
      have hl : raw29860step1Labels = raw29860step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3439 node3439Labels := by rfl

def raw29861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw29861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29861 raw29861Labels = mixedMoment B node2910 node2910Labels := by
  calc
    mixedMoment B raw29861 raw29861Labels = mixedMoment B raw29861step0 raw29861step0Labels := by
      have hz : ∀ j, raw29861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29861step0 = (fun i j => raw29861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29861step0 raw29861; decide +kernel
      have hl : raw29861step0Labels = raw29861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29861 raw29861Labels permutation346 hz
    mixedMoment B raw29861step0 raw29861step0Labels = mixedMoment B raw29861step1 raw29861step1Labels := by
      have ha : raw29861step1 = (fun i j => raw29861step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29861step1 raw29861step0; decide +kernel
      have hl : raw29861step1Labels = raw29861step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29861step0 raw29861step0Labels permutation33 permutation2
    _ = mixedMoment B node2910 node2910Labels := by rfl

def raw29862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw29862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw29862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29862 raw29862Labels = mixedMoment B node3349 node3349Labels := by
  calc
    mixedMoment B raw29862 raw29862Labels = mixedMoment B raw29862step0 raw29862step0Labels := by
      have hz : ∀ j, raw29862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29862step0 = (fun i j => raw29862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29862step0 raw29862; decide +kernel
      have hl : raw29862step0Labels = raw29862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29862 raw29862Labels permutation346 hz
    mixedMoment B raw29862step0 raw29862step0Labels = mixedMoment B raw29862step1 raw29862step1Labels := by
      have ha : raw29862step1 = (fun i j => raw29862step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29862step1 raw29862step0; decide +kernel
      have hl : raw29862step1Labels = raw29862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29862step0 raw29862step0Labels permutation126 permutation2
    mixedMoment B raw29862step1 raw29862step1Labels = mixedMoment B raw29862step2 raw29862step2Labels := by
      have ha : raw29862step2 = -raw29862step1 := by apply Matrix.ext; change ∀ i j, raw29862step2 i j = -(raw29862step1 i j); unfold raw29862step2 raw29862step1; decide +kernel
      have hl : raw29862step2Labels = raw29862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3349 node3349Labels := by rfl

def raw29863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29863 raw29863Labels = mixedMoment B node3346 node3346Labels := by
  calc
    mixedMoment B raw29863 raw29863Labels = mixedMoment B raw29863step0 raw29863step0Labels := by
      have ha : raw29863step0 = (fun i j => raw29863 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29863step0 raw29863; decide +kernel
      have hl : raw29863step0Labels = raw29863Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29863 raw29863Labels permutation589 permutation2
    mixedMoment B raw29863step0 raw29863step0Labels = mixedMoment B raw29863step1 raw29863step1Labels := by
      have ha : raw29863step1 = -raw29863step0 := by apply Matrix.ext; change ∀ i j, raw29863step1 i j = -(raw29863step0 i j); unfold raw29863step1 raw29863step0; decide +kernel
      have hl : raw29863step1Labels = raw29863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3346 node3346Labels := by rfl

def raw29864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw29864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw29864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29864 raw29864Labels = mixedMoment B node3357 node3357Labels := by
  calc
    mixedMoment B raw29864 raw29864Labels = mixedMoment B raw29864step0 raw29864step0Labels := by
      have hz : ∀ j, raw29864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29864step0 = (fun i j => raw29864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29864step0 raw29864; decide +kernel
      have hl : raw29864step0Labels = raw29864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29864 raw29864Labels permutation346 hz
    mixedMoment B raw29864step0 raw29864step0Labels = mixedMoment B raw29864step1 raw29864step1Labels := by
      have ha : raw29864step1 = (fun i j => raw29864step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29864step1 raw29864step0; decide +kernel
      have hl : raw29864step1Labels = raw29864step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29864step0 raw29864step0Labels permutation125 permutation2
    mixedMoment B raw29864step1 raw29864step1Labels = mixedMoment B raw29864step2 raw29864step2Labels := by
      have ha : raw29864step2 = -raw29864step1 := by apply Matrix.ext; change ∀ i j, raw29864step2 i j = -(raw29864step1 i j); unfold raw29864step2 raw29864step1; decide +kernel
      have hl : raw29864step2Labels = raw29864step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3357 node3357Labels := by rfl

def raw29865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw29865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw29865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw29865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw29865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29865 raw29865Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw29865 raw29865Labels = mixedMoment B raw29865step0 raw29865step0Labels := by
      have hz : ∀ j, raw29865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29865step0 = (fun i j => raw29865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29865step0 raw29865; decide +kernel
      have hl : raw29865step0Labels = raw29865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29865 raw29865Labels permutation346 hz
    mixedMoment B raw29865step0 raw29865step0Labels = mixedMoment B raw29865step1 raw29865step1Labels := by
      have ha : raw29865step1 = (fun i j => raw29865step0 (permutation105 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29865step1 raw29865step0; decide +kernel
      have hl : raw29865step1Labels = raw29865step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29865step0 raw29865step0Labels permutation105 permutation4
    mixedMoment B raw29865step1 raw29865step1Labels = mixedMoment B raw29865step2 raw29865step2Labels := by
      have ha : raw29865step2 = -raw29865step1 := by apply Matrix.ext; change ∀ i j, raw29865step2 i j = -(raw29865step1 i j); unfold raw29865step2 raw29865step1; decide +kernel
      have hl : raw29865step2Labels = raw29865step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw29866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw29866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw29866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw29866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw29866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29866 raw29866Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw29866 raw29866Labels = mixedMoment B raw29866step0 raw29866step0Labels := by
      have hz : ∀ j, raw29866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29866step0 = (fun i j => raw29866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29866step0 raw29866; decide +kernel
      have hl : raw29866step0Labels = raw29866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29866 raw29866Labels permutation346 hz
    mixedMoment B raw29866step0 raw29866step0Labels = mixedMoment B raw29866step1 raw29866step1Labels := by
      have ha : raw29866step1 = (fun i j => raw29866step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29866step1 raw29866step0; decide +kernel
      have hl : raw29866step1Labels = raw29866step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29866step0 raw29866step0Labels permutation127 permutation2
    mixedMoment B raw29866step1 raw29866step1Labels = mixedMoment B raw29866step2 raw29866step2Labels := by
      have ha : raw29866step2 = -raw29866step1 := by apply Matrix.ext; change ∀ i j, raw29866step2 i j = -(raw29866step1 i j); unfold raw29866step2 raw29866step1; decide +kernel
      have hl : raw29866step2Labels = raw29866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3479 node3479Labels := by rfl

def raw29867 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-2, 2], ![3, -3], ![1, -1]]
def raw29867Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29867step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![3, -3], ![1, -1]]
def raw29867step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29867step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29867step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29867step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29867step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29867 raw29867Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw29867 raw29867Labels = mixedMoment B raw29867step0 raw29867step0Labels := by
      have hz : ∀ j, raw29867 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29867step0 = (fun i j => raw29867 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29867step0 raw29867; decide +kernel
      have hl : raw29867step0Labels = raw29867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29867 raw29867Labels permutation346 hz
    mixedMoment B raw29867step0 raw29867step0Labels = mixedMoment B raw29867step1 raw29867step1Labels := by
      have ha : raw29867step1 = (fun i j => raw29867step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29867step1 raw29867step0; decide +kernel
      have hl : raw29867step1Labels = raw29867step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29867step0 raw29867step0Labels permutation122 permutation0
    mixedMoment B raw29867step1 raw29867step1Labels = mixedMoment B raw29867step2 raw29867step2Labels := by
      have ha : raw29867step2 = -raw29867step1 := by apply Matrix.ext; change ∀ i j, raw29867step2 i j = -(raw29867step1 i j); unfold raw29867step2 raw29867step1; decide +kernel
      have hl : raw29867step2Labels = raw29867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw29868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw29868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw29868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29868 raw29868Labels = mixedMoment B node3665 node3665Labels := by
  calc
    mixedMoment B raw29868 raw29868Labels = mixedMoment B raw29868step0 raw29868step0Labels := by
      have hz : ∀ j, raw29868 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29868step0 = (fun i j => raw29868 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29868step0 raw29868; decide +kernel
      have hl : raw29868step0Labels = raw29868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29868 raw29868Labels permutation346 hz
    mixedMoment B raw29868step0 raw29868step0Labels = mixedMoment B raw29868step1 raw29868step1Labels := by
      have ha : raw29868step1 = (fun i j => raw29868step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29868step1 raw29868step0; decide +kernel
      have hl : raw29868step1Labels = raw29868step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29868step0 raw29868step0Labels permutation125 permutation2
    mixedMoment B raw29868step1 raw29868step1Labels = mixedMoment B raw29868step2 raw29868step2Labels := by
      have ha : raw29868step2 = -raw29868step1 := by apply Matrix.ext; change ∀ i j, raw29868step2 i j = -(raw29868step1 i j); unfold raw29868step2 raw29868step1; decide +kernel
      have hl : raw29868step2Labels = raw29868step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3665 node3665Labels := by rfl

def raw29869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29869 raw29869Labels = mixedMoment B node2856 node2856Labels := by
  calc
    mixedMoment B raw29869 raw29869Labels = mixedMoment B raw29869step0 raw29869step0Labels := by
      have hz : ∀ j, raw29869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29869step0 = (fun i j => raw29869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29869step0 raw29869; decide +kernel
      have hl : raw29869step0Labels = raw29869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29869 raw29869Labels permutation346 hz
    mixedMoment B raw29869step0 raw29869step0Labels = mixedMoment B raw29869step1 raw29869step1Labels := by
      have ha : raw29869step1 = (fun i j => raw29869step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29869step1 raw29869step0; decide +kernel
      have hl : raw29869step1Labels = raw29869step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29869step0 raw29869step0Labels permutation38 permutation2
    _ = mixedMoment B node2856 node2856Labels := by rfl

def raw29870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw29870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29870 raw29870Labels = mixedMoment B node2844 node2844Labels := by
  calc
    mixedMoment B raw29870 raw29870Labels = mixedMoment B raw29870step0 raw29870step0Labels := by
      have ha : raw29870step0 = (fun i j => raw29870 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29870step0 raw29870; decide +kernel
      have hl : raw29870step0Labels = raw29870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29870 raw29870Labels permutation200 permutation2
    _ = mixedMoment B node2844 node2844Labels := by rfl

def raw29871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw29871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw29871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29871 raw29871Labels = mixedMoment B node2310 node2310Labels := by
  calc
    mixedMoment B raw29871 raw29871Labels = mixedMoment B raw29871step0 raw29871step0Labels := by
      have hz : ∀ j, raw29871 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29871step0 = (fun i j => raw29871 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29871step0 raw29871; decide +kernel
      have hl : raw29871step0Labels = raw29871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29871 raw29871Labels permutation346 hz
    mixedMoment B raw29871step0 raw29871step0Labels = mixedMoment B raw29871step1 raw29871step1Labels := by
      have ha : raw29871step1 = (fun i j => raw29871step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29871step1 raw29871step0; decide +kernel
      have hl : raw29871step1Labels = raw29871step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29871step0 raw29871step0Labels permutation125 permutation2
    mixedMoment B raw29871step1 raw29871step1Labels = mixedMoment B raw29871step2 raw29871step2Labels := by
      have ha : raw29871step2 = -raw29871step1 := by apply Matrix.ext; change ∀ i j, raw29871step2 i j = -(raw29871step1 i j); unfold raw29871step2 raw29871step1; decide +kernel
      have hl : raw29871step2Labels = raw29871step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2310 node2310Labels := by rfl

def raw29872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw29872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw29872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29872 raw29872Labels = mixedMoment B node2310 node2310Labels := by
  calc
    mixedMoment B raw29872 raw29872Labels = mixedMoment B raw29872step0 raw29872step0Labels := by
      have hz : ∀ j, raw29872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29872step0 = (fun i j => raw29872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29872step0 raw29872; decide +kernel
      have hl : raw29872step0Labels = raw29872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29872 raw29872Labels permutation346 hz
    mixedMoment B raw29872step0 raw29872step0Labels = mixedMoment B raw29872step1 raw29872step1Labels := by
      have ha : raw29872step1 = (fun i j => raw29872step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29872step1 raw29872step0; decide +kernel
      have hl : raw29872step1Labels = raw29872step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29872step0 raw29872step0Labels permutation149 permutation2
    mixedMoment B raw29872step1 raw29872step1Labels = mixedMoment B raw29872step2 raw29872step2Labels := by
      have ha : raw29872step2 = -raw29872step1 := by apply Matrix.ext; change ∀ i j, raw29872step2 i j = -(raw29872step1 i j); unfold raw29872step2 raw29872step1; decide +kernel
      have hl : raw29872step2Labels = raw29872step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2310 node2310Labels := by rfl

def raw29873 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-2, 2, 0]]
def raw29873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def raw29873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29873 raw29873Labels = mixedMoment B node3611 node3611Labels := by
  calc
    mixedMoment B raw29873 raw29873Labels = mixedMoment B raw29873step0 raw29873step0Labels := by
      have hz : ∀ j, raw29873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29873step0 = (fun i j => raw29873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29873step0 raw29873; decide +kernel
      have hl : raw29873step0Labels = raw29873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29873 raw29873Labels permutation346 hz
    mixedMoment B raw29873step0 raw29873step0Labels = mixedMoment B raw29873step1 raw29873step1Labels := by
      have ha : raw29873step1 = (fun i j => raw29873step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29873step1 raw29873step0; decide +kernel
      have hl : raw29873step1Labels = raw29873step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29873step0 raw29873step0Labels permutation35 permutation4
    mixedMoment B raw29873step1 raw29873step1Labels = mixedMoment B raw29873step2 raw29873step2Labels := by
      have ha : raw29873step2 = -raw29873step1 := by apply Matrix.ext; change ∀ i j, raw29873step2 i j = -(raw29873step1 i j); unfold raw29873step2 raw29873step1; decide +kernel
      have hl : raw29873step2Labels = raw29873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3611 node3611Labels := by rfl

def raw29874 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw29874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29874 raw29874Labels = mixedMoment B node3362 node3362Labels := by
  calc
    mixedMoment B raw29874 raw29874Labels = mixedMoment B raw29874step0 raw29874step0Labels := by
      have ha : raw29874step0 = (fun i j => raw29874 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29874step0 raw29874; decide +kernel
      have hl : raw29874step0Labels = raw29874Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29874 raw29874Labels permutation200 permutation2
    mixedMoment B raw29874step0 raw29874step0Labels = mixedMoment B raw29874step1 raw29874step1Labels := by
      have ha : raw29874step1 = -raw29874step0 := by apply Matrix.ext; change ∀ i j, raw29874step1 i j = -(raw29874step0 i j); unfold raw29874step1 raw29874step0; decide +kernel
      have hl : raw29874step1Labels = raw29874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3362 node3362Labels := by rfl

def raw29875 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![-2, 0, 2]]
def raw29875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![2, -2, 0], ![-3, 1, 2], ![-2, 0, 2]]
def raw29875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29875 raw29875Labels = mixedMoment B node2311 node2311Labels := by
  calc
    mixedMoment B raw29875 raw29875Labels = mixedMoment B raw29875step0 raw29875step0Labels := by
      have hz : ∀ j, raw29875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29875step0 = (fun i j => raw29875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29875step0 raw29875; decide +kernel
      have hl : raw29875step0Labels = raw29875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29875 raw29875Labels permutation346 hz
    mixedMoment B raw29875step0 raw29875step0Labels = mixedMoment B raw29875step1 raw29875step1Labels := by
      have ha : raw29875step1 = (fun i j => raw29875step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29875step1 raw29875step0; decide +kernel
      have hl : raw29875step1Labels = raw29875step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29875step0 raw29875step0Labels permutation125 permutation2
    _ = mixedMoment B node2311 node2311Labels := by rfl

def raw29876 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw29876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw29876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29876 raw29876Labels = mixedMoment B node2311 node2311Labels := by
  calc
    mixedMoment B raw29876 raw29876Labels = mixedMoment B raw29876step0 raw29876step0Labels := by
      have hz : ∀ j, raw29876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29876step0 = (fun i j => raw29876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29876step0 raw29876; decide +kernel
      have hl : raw29876step0Labels = raw29876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29876 raw29876Labels permutation346 hz
    mixedMoment B raw29876step0 raw29876step0Labels = mixedMoment B raw29876step1 raw29876step1Labels := by
      have ha : raw29876step1 = (fun i j => raw29876step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29876step1 raw29876step0; decide +kernel
      have hl : raw29876step1Labels = raw29876step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29876step0 raw29876step0Labels permutation149 permutation2
    _ = mixedMoment B node2311 node2311Labels := by rfl

def raw29877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw29877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29877 raw29877Labels = mixedMoment B node2912 node2912Labels := by
  calc
    mixedMoment B raw29877 raw29877Labels = mixedMoment B raw29877step0 raw29877step0Labels := by
      have ha : raw29877step0 = (fun i j => raw29877 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29877step0 raw29877; decide +kernel
      have hl : raw29877step0Labels = raw29877Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29877 raw29877Labels permutation153 permutation2
    _ = mixedMoment B node2912 node2912Labels := by rfl

def raw29878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw29878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw29878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29878step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29878 raw29878Labels = mixedMoment B node3338 node3338Labels := by
  calc
    mixedMoment B raw29878 raw29878Labels = mixedMoment B raw29878step0 raw29878step0Labels := by
      have ha : raw29878step0 = (fun i j => raw29878 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29878step0 raw29878; decide +kernel
      have hl : raw29878step0Labels = raw29878Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29878 raw29878Labels permutation583 permutation2
    mixedMoment B raw29878step0 raw29878step0Labels = mixedMoment B raw29878step1 raw29878step1Labels := by
      have ha : raw29878step1 = -raw29878step0 := by apply Matrix.ext; change ∀ i j, raw29878step1 i j = -(raw29878step0 i j); unfold raw29878step1 raw29878step0; decide +kernel
      have hl : raw29878step1Labels = raw29878step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3338 node3338Labels := by rfl

def raw29879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw29879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29879 raw29879Labels = mixedMoment B node3341 node3341Labels := by
  calc
    mixedMoment B raw29879 raw29879Labels = mixedMoment B raw29879step0 raw29879step0Labels := by
      have ha : raw29879step0 = (fun i j => raw29879 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29879step0 raw29879; decide +kernel
      have hl : raw29879step0Labels = raw29879Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29879 raw29879Labels permutation587 permutation2
    mixedMoment B raw29879step0 raw29879step0Labels = mixedMoment B raw29879step1 raw29879step1Labels := by
      have ha : raw29879step1 = -raw29879step0 := by apply Matrix.ext; change ∀ i j, raw29879step1 i j = -(raw29879step0 i j); unfold raw29879step1 raw29879step0; decide +kernel
      have hl : raw29879step1Labels = raw29879step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3341 node3341Labels := by rfl

def raw29880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw29880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29880step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29880 raw29880Labels = mixedMoment B node3341 node3341Labels := by
  calc
    mixedMoment B raw29880 raw29880Labels = mixedMoment B raw29880step0 raw29880step0Labels := by
      have ha : raw29880step0 = (fun i j => raw29880 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29880step0 raw29880; decide +kernel
      have hl : raw29880step0Labels = raw29880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29880 raw29880Labels permutation582 permutation2
    mixedMoment B raw29880step0 raw29880step0Labels = mixedMoment B raw29880step1 raw29880step1Labels := by
      have ha : raw29880step1 = -raw29880step0 := by apply Matrix.ext; change ∀ i j, raw29880step1 i j = -(raw29880step0 i j); unfold raw29880step1 raw29880step0; decide +kernel
      have hl : raw29880step1Labels = raw29880step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3341 node3341Labels := by rfl

def raw29881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw29881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw29881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw29881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29881 raw29881Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw29881 raw29881Labels = mixedMoment B raw29881step0 raw29881step0Labels := by
      have ha : raw29881step0 = (fun i j => raw29881 (permutation524 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29881step0 raw29881; decide +kernel
      have hl : raw29881step0Labels = raw29881Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29881 raw29881Labels permutation524 permutation4
    mixedMoment B raw29881step0 raw29881step0Labels = mixedMoment B raw29881step1 raw29881step1Labels := by
      have ha : raw29881step1 = -raw29881step0 := by apply Matrix.ext; change ∀ i j, raw29881step1 i j = -(raw29881step0 i j); unfold raw29881step1 raw29881step0; decide +kernel
      have hl : raw29881step1Labels = raw29881step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw29882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw29882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29882 raw29882Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw29882 raw29882Labels = mixedMoment B raw29882step0 raw29882step0Labels := by
      have ha : raw29882step0 = (fun i j => raw29882 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29882step0 raw29882; decide +kernel
      have hl : raw29882step0Labels = raw29882Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29882 raw29882Labels permutation584 permutation2
    mixedMoment B raw29882step0 raw29882step0Labels = mixedMoment B raw29882step1 raw29882step1Labels := by
      have ha : raw29882step1 = -raw29882step0 := by apply Matrix.ext; change ∀ i j, raw29882step1 i j = -(raw29882step0 i j); unfold raw29882step1 raw29882step0; decide +kernel
      have hl : raw29882step1Labels = raw29882step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3460 node3460Labels := by rfl

def raw29883 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![3, -3], ![1, -1]]
def raw29883Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29883step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw29883step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29883step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw29883step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29883 raw29883Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw29883 raw29883Labels = mixedMoment B raw29883step0 raw29883step0Labels := by
      have ha : raw29883step0 = (fun i j => raw29883 (permutation569 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29883step0 raw29883; decide +kernel
      have hl : raw29883step0Labels = raw29883Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29883 raw29883Labels permutation569 permutation0
    mixedMoment B raw29883step0 raw29883step0Labels = mixedMoment B raw29883step1 raw29883step1Labels := by
      have ha : raw29883step1 = -raw29883step0 := by apply Matrix.ext; change ∀ i j, raw29883step1 i j = -(raw29883step0 i j); unfold raw29883step1 raw29883step0; decide +kernel
      have hl : raw29883step1Labels = raw29883step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw29884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw29884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29884 raw29884Labels = mixedMoment B node3647 node3647Labels := by
  calc
    mixedMoment B raw29884 raw29884Labels = mixedMoment B raw29884step0 raw29884step0Labels := by
      have ha : raw29884step0 = (fun i j => raw29884 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29884step0 raw29884; decide +kernel
      have hl : raw29884step0Labels = raw29884Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29884 raw29884Labels permutation583 permutation2
    mixedMoment B raw29884step0 raw29884step0Labels = mixedMoment B raw29884step1 raw29884step1Labels := by
      have ha : raw29884step1 = -raw29884step0 := by apply Matrix.ext; change ∀ i j, raw29884step1 i j = -(raw29884step0 i j); unfold raw29884step1 raw29884step0; decide +kernel
      have hl : raw29884step1Labels = raw29884step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3647 node3647Labels := by rfl

def raw29885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29885 raw29885Labels = mixedMoment B node3652 node3652Labels := by
  calc
    mixedMoment B raw29885 raw29885Labels = mixedMoment B raw29885step0 raw29885step0Labels := by
      have ha : raw29885step0 = (fun i j => raw29885 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29885step0 raw29885; decide +kernel
      have hl : raw29885step0Labels = raw29885Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29885 raw29885Labels permutation587 permutation2
    mixedMoment B raw29885step0 raw29885step0Labels = mixedMoment B raw29885step1 raw29885step1Labels := by
      have ha : raw29885step1 = -raw29885step0 := by apply Matrix.ext; change ∀ i j, raw29885step1 i j = -(raw29885step0 i j); unfold raw29885step1 raw29885step0; decide +kernel
      have hl : raw29885step1Labels = raw29885step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3652 node3652Labels := by rfl

def raw29886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29886 raw29886Labels = mixedMoment B node3652 node3652Labels := by
  calc
    mixedMoment B raw29886 raw29886Labels = mixedMoment B raw29886step0 raw29886step0Labels := by
      have ha : raw29886step0 = (fun i j => raw29886 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29886step0 raw29886; decide +kernel
      have hl : raw29886step0Labels = raw29886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29886 raw29886Labels permutation582 permutation2
    mixedMoment B raw29886step0 raw29886step0Labels = mixedMoment B raw29886step1 raw29886step1Labels := by
      have ha : raw29886step1 = -raw29886step0 := by apply Matrix.ext; change ∀ i j, raw29886step1 i j = -(raw29886step0 i j); unfold raw29886step1 raw29886step0; decide +kernel
      have hl : raw29886step1Labels = raw29886step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3652 node3652Labels := by rfl

def raw29887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw29887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29887 raw29887Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw29887 raw29887Labels = mixedMoment B raw29887step0 raw29887step0Labels := by
      have ha : raw29887step0 = (fun i j => raw29887 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29887step0 raw29887; decide +kernel
      have hl : raw29887step0Labels = raw29887Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29887 raw29887Labels permutation584 permutation2
    mixedMoment B raw29887step0 raw29887step0Labels = mixedMoment B raw29887step1 raw29887step1Labels := by
      have ha : raw29887step1 = -raw29887step0 := by apply Matrix.ext; change ∀ i j, raw29887step1 i j = -(raw29887step0 i j); unfold raw29887step1 raw29887step0; decide +kernel
      have hl : raw29887step1Labels = raw29887step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3758 node3758Labels := by rfl

def raw29888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29888 raw29888Labels = mixedMoment B node2891 node2891Labels := by
  calc
    _ = mixedMoment B node2891 node2891Labels := by rfl

def raw29889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw29889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29889 raw29889Labels = mixedMoment B node2297 node2297Labels := by
  calc
    mixedMoment B raw29889 raw29889Labels = mixedMoment B raw29889step0 raw29889step0Labels := by
      have ha : raw29889step0 = (fun i j => raw29889 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29889step0 raw29889; decide +kernel
      have hl : raw29889step0Labels = raw29889Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29889 raw29889Labels permutation587 permutation2
    mixedMoment B raw29889step0 raw29889step0Labels = mixedMoment B raw29889step1 raw29889step1Labels := by
      have ha : raw29889step1 = -raw29889step0 := by apply Matrix.ext; change ∀ i j, raw29889step1 i j = -(raw29889step0 i j); unfold raw29889step1 raw29889step0; decide +kernel
      have hl : raw29889step1Labels = raw29889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2297 node2297Labels := by rfl

def raw29890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw29890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29890 raw29890Labels = mixedMoment B node2297 node2297Labels := by
  calc
    mixedMoment B raw29890 raw29890Labels = mixedMoment B raw29890step0 raw29890step0Labels := by
      have ha : raw29890step0 = (fun i j => raw29890 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29890step0 raw29890; decide +kernel
      have hl : raw29890step0Labels = raw29890Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29890 raw29890Labels permutation686 permutation2
    mixedMoment B raw29890step0 raw29890step0Labels = mixedMoment B raw29890step1 raw29890step1Labels := by
      have ha : raw29890step1 = -raw29890step0 := by apply Matrix.ext; change ∀ i j, raw29890step1 i j = -(raw29890step0 i j); unfold raw29890step1 raw29890step0; decide +kernel
      have hl : raw29890step1Labels = raw29890step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2297 node2297Labels := by rfl

def raw29891 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw29891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29891 raw29891Labels = mixedMoment B node3439 node3439Labels := by
  calc
    mixedMoment B raw29891 raw29891Labels = mixedMoment B raw29891step0 raw29891step0Labels := by
      have hz : ∀ j, raw29891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29891step0 = (fun i j => raw29891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29891step0 raw29891; decide +kernel
      have hl : raw29891step0Labels = raw29891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29891 raw29891Labels permutation434 hz
    mixedMoment B raw29891step0 raw29891step0Labels = mixedMoment B raw29891step1 raw29891step1Labels := by
      have ha : raw29891step1 = -raw29891step0 := by apply Matrix.ext; change ∀ i j, raw29891step1 i j = -(raw29891step0 i j); unfold raw29891step1 raw29891step0; decide +kernel
      have hl : raw29891step1Labels = raw29891step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3439 node3439Labels := by rfl

def raw29892 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-2, 0, 2]]
def raw29892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29892 raw29892Labels = mixedMoment B node2302 node2302Labels := by
  calc
    mixedMoment B raw29892 raw29892Labels = mixedMoment B raw29892step0 raw29892step0Labels := by
      have ha : raw29892step0 = (fun i j => raw29892 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29892step0 raw29892; decide +kernel
      have hl : raw29892step0Labels = raw29892Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29892 raw29892Labels permutation584 permutation2
    _ = mixedMoment B node2302 node2302Labels := by rfl

def raw29893 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw29893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29893 raw29893Labels = mixedMoment B node2302 node2302Labels := by
  calc
    mixedMoment B raw29893 raw29893Labels = mixedMoment B raw29893step0 raw29893step0Labels := by
      have ha : raw29893step0 = (fun i j => raw29893 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29893step0 raw29893; decide +kernel
      have hl : raw29893step0Labels = raw29893Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29893 raw29893Labels permutation682 permutation2
    _ = mixedMoment B node2302 node2302Labels := by rfl

def raw29894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29894 raw29894Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw29894 raw29894Labels = mixedMoment B raw29894step0 raw29894step0Labels := by
      have hz : ∀ j, raw29894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29894step0 = (fun i j => raw29894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29894step0 raw29894; decide +kernel
      have hl : raw29894step0Labels = raw29894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29894 raw29894Labels permutation434 hz
    mixedMoment B raw29894step0 raw29894step0Labels = mixedMoment B raw29894step1 raw29894step1Labels := by
      have ha : raw29894step1 = (fun i j => raw29894step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29894step1 raw29894step0; decide +kernel
      have hl : raw29894step1Labels = raw29894step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29894step0 raw29894step0Labels permutation149 permutation2
    mixedMoment B raw29894step1 raw29894step1Labels = mixedMoment B raw29894step2 raw29894step2Labels := by
      have ha : raw29894step2 = -raw29894step1 := by apply Matrix.ext; change ∀ i j, raw29894step2 i j = -(raw29894step1 i j); unfold raw29894step2 raw29894step1; decide +kernel
      have hl : raw29894step2Labels = raw29894step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw29895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29895 raw29895Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw29895 raw29895Labels = mixedMoment B raw29895step0 raw29895step0Labels := by
      have hz : ∀ j, raw29895 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29895step0 = (fun i j => raw29895 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29895step0 raw29895; decide +kernel
      have hl : raw29895step0Labels = raw29895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29895 raw29895Labels permutation434 hz
    mixedMoment B raw29895step0 raw29895step0Labels = mixedMoment B raw29895step1 raw29895step1Labels := by
      have ha : raw29895step1 = (fun i j => raw29895step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29895step1 raw29895step0; decide +kernel
      have hl : raw29895step1Labels = raw29895step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29895step0 raw29895step0Labels permutation38 permutation2
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw29896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29896 raw29896Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw29896 raw29896Labels = mixedMoment B raw29896step0 raw29896step0Labels := by
      have hz : ∀ j, raw29896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29896step0 = (fun i j => raw29896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29896step0 raw29896; decide +kernel
      have hl : raw29896step0Labels = raw29896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29896 raw29896Labels permutation434 hz
    _ = mixedMoment B node2620 node2620Labels := by rfl

def raw29897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29897 raw29897Labels = mixedMoment B node2438 node2438Labels := by
  calc
    mixedMoment B raw29897 raw29897Labels = mixedMoment B raw29897step0 raw29897step0Labels := by
      have ha : raw29897step0 = (fun i j => raw29897 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29897step0 raw29897; decide +kernel
      have hl : raw29897step0Labels = raw29897Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29897 raw29897Labels permutation176 permutation2
    _ = mixedMoment B node2438 node2438Labels := by rfl

def raw29898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw29898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29898 raw29898Labels = mixedMoment B node2443 node2443Labels := by
  calc
    mixedMoment B raw29898 raw29898Labels = mixedMoment B raw29898step0 raw29898step0Labels := by
      have hz : ∀ j, raw29898 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29898step0 = (fun i j => raw29898 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29898step0 raw29898; decide +kernel
      have hl : raw29898step0Labels = raw29898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29898 raw29898Labels permutation434 hz
    mixedMoment B raw29898step0 raw29898step0Labels = mixedMoment B raw29898step1 raw29898step1Labels := by
      have ha : raw29898step1 = (fun i j => raw29898step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29898step1 raw29898step0; decide +kernel
      have hl : raw29898step1Labels = raw29898step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29898step0 raw29898step0Labels permutation39 permutation2
    _ = mixedMoment B node2443 node2443Labels := by rfl

def raw29899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw29899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![3, -1, -2]]
def raw29899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29899 raw29899Labels = mixedMoment B node2355 node2355Labels := by
  calc
    mixedMoment B raw29899 raw29899Labels = mixedMoment B raw29899step0 raw29899step0Labels := by
      have hz : ∀ j, raw29899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29899step0 = (fun i j => raw29899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29899step0 raw29899; decide +kernel
      have hl : raw29899step0Labels = raw29899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29899 raw29899Labels permutation434 hz
    mixedMoment B raw29899step0 raw29899step0Labels = mixedMoment B raw29899step1 raw29899step1Labels := by
      have ha : raw29899step1 = (fun i j => raw29899step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29899step1 raw29899step0; decide +kernel
      have hl : raw29899step1Labels = raw29899step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29899step0 raw29899step0Labels permutation149 permutation2
    mixedMoment B raw29899step1 raw29899step1Labels = mixedMoment B raw29899step2 raw29899step2Labels := by
      have ha : raw29899step2 = -raw29899step1 := by apply Matrix.ext; change ∀ i j, raw29899step2 i j = -(raw29899step1 i j); unfold raw29899step2 raw29899step1; decide +kernel
      have hl : raw29899step2Labels = raw29899step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2355 node2355Labels := by rfl

def raw29900 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]
def raw29900Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29900step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]
def raw29900step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29900step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw29900step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29900step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw29900step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29900 raw29900Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw29900 raw29900Labels = mixedMoment B raw29900step0 raw29900step0Labels := by
      have hz : ∀ j, raw29900 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29900step0 = (fun i j => raw29900 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29900step0 raw29900; decide +kernel
      have hl : raw29900step0Labels = raw29900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29900 raw29900Labels permutation520 hz
    mixedMoment B raw29900step0 raw29900step0Labels = mixedMoment B raw29900step1 raw29900step1Labels := by
      have hz : ∀ j, raw29900step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29900step1 = (fun i j => raw29900step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29900step1 raw29900step0; decide +kernel
      have hl : raw29900step1Labels = raw29900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29900step0 raw29900step0Labels permutation104 hz
    mixedMoment B raw29900step1 raw29900step1Labels = mixedMoment B raw29900step2 raw29900step2Labels := by
      have ha : raw29900step2 = (fun i j => raw29900step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29900step2 raw29900step1; decide +kernel
      have hl : raw29900step2Labels = raw29900step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29900step1 raw29900step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw29901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw29901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29901 raw29901Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw29901 raw29901Labels = mixedMoment B raw29901step0 raw29901step0Labels := by
      have hz : ∀ j, raw29901 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29901step0 = (fun i j => raw29901 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29901step0 raw29901; decide +kernel
      have hl : raw29901step0Labels = raw29901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29901 raw29901Labels permutation434 hz
    mixedMoment B raw29901step0 raw29901step0Labels = mixedMoment B raw29901step1 raw29901step1Labels := by
      have ha : raw29901step1 = (fun i j => raw29901step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29901step1 raw29901step0; decide +kernel
      have hl : raw29901step1Labels = raw29901step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29901step0 raw29901step0Labels permutation57 permutation2
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw29902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw29902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29902 raw29902Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw29902 raw29902Labels = mixedMoment B raw29902step0 raw29902step0Labels := by
      have hz : ∀ j, raw29902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29902step0 = (fun i j => raw29902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29902step0 raw29902; decide +kernel
      have hl : raw29902step0Labels = raw29902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29902 raw29902Labels permutation434 hz
    mixedMoment B raw29902step0 raw29902step0Labels = mixedMoment B raw29902step1 raw29902step1Labels := by
      have ha : raw29902step1 = (fun i j => raw29902step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29902step1 raw29902step0; decide +kernel
      have hl : raw29902step1Labels = raw29902step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29902step0 raw29902step0Labels permutation33 permutation2
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw29903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw29903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29903 raw29903Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw29903 raw29903Labels = mixedMoment B raw29903step0 raw29903step0Labels := by
      have hz : ∀ j, raw29903 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29903step0 = (fun i j => raw29903 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29903step0 raw29903; decide +kernel
      have hl : raw29903step0Labels = raw29903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29903 raw29903Labels permutation434 hz
    mixedMoment B raw29903step0 raw29903step0Labels = mixedMoment B raw29903step1 raw29903step1Labels := by
      have ha : raw29903step1 = (fun i j => raw29903step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29903step1 raw29903step0; decide +kernel
      have hl : raw29903step1Labels = raw29903step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29903step0 raw29903step0Labels permutation33 permutation2
    _ = mixedMoment B node2817 node2817Labels := by rfl

def raw29904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29904 raw29904Labels = mixedMoment B node2798 node2798Labels := by
  calc
    mixedMoment B raw29904 raw29904Labels = mixedMoment B raw29904step0 raw29904step0Labels := by
      have ha : raw29904step0 = (fun i j => raw29904 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29904step0 raw29904; decide +kernel
      have hl : raw29904step0Labels = raw29904Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29904 raw29904Labels permutation153 permutation2
    _ = mixedMoment B node2798 node2798Labels := by rfl

def raw29905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw29905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29905step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29905 raw29905Labels = mixedMoment B node2352 node2352Labels := by
  calc
    mixedMoment B raw29905 raw29905Labels = mixedMoment B raw29905step0 raw29905step0Labels := by
      have hz : ∀ j, raw29905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29905step0 = (fun i j => raw29905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29905step0 raw29905; decide +kernel
      have hl : raw29905step0Labels = raw29905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29905 raw29905Labels permutation434 hz
    mixedMoment B raw29905step0 raw29905step0Labels = mixedMoment B raw29905step1 raw29905step1Labels := by
      have ha : raw29905step1 = (fun i j => raw29905step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29905step1 raw29905step0; decide +kernel
      have hl : raw29905step1Labels = raw29905step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29905step0 raw29905step0Labels permutation127 permutation2
    mixedMoment B raw29905step1 raw29905step1Labels = mixedMoment B raw29905step2 raw29905step2Labels := by
      have ha : raw29905step2 = -raw29905step1 := by apply Matrix.ext; change ∀ i j, raw29905step2 i j = -(raw29905step1 i j); unfold raw29905step2 raw29905step1; decide +kernel
      have hl : raw29905step2Labels = raw29905step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2352 node2352Labels := by rfl

def raw29906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw29906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29906 raw29906Labels = mixedMoment B node2803 node2803Labels := by
  calc
    mixedMoment B raw29906 raw29906Labels = mixedMoment B raw29906step0 raw29906step0Labels := by
      have hz : ∀ j, raw29906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29906step0 = (fun i j => raw29906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29906step0 raw29906; decide +kernel
      have hl : raw29906step0Labels = raw29906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29906 raw29906Labels permutation434 hz
    _ = mixedMoment B node2803 node2803Labels := by rfl

def raw29907 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]
def raw29907Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29907step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]
def raw29907step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29907step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw29907step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29907step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw29907step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29907 raw29907Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw29907 raw29907Labels = mixedMoment B raw29907step0 raw29907step0Labels := by
      have hz : ∀ j, raw29907 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw29907step0 = (fun i j => raw29907 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw29907step0 raw29907; decide +kernel
      have hl : raw29907step0Labels = raw29907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29907 raw29907Labels permutation590 hz
    mixedMoment B raw29907step0 raw29907step0Labels = mixedMoment B raw29907step1 raw29907step1Labels := by
      have hz : ∀ j, raw29907step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29907step1 = (fun i j => raw29907step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29907step1 raw29907step0; decide +kernel
      have hl : raw29907step1Labels = raw29907step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29907step0 raw29907step0Labels permutation104 hz
    mixedMoment B raw29907step1 raw29907step1Labels = mixedMoment B raw29907step2 raw29907step2Labels := by
      have ha : raw29907step2 = (fun i j => raw29907step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29907step2 raw29907step1; decide +kernel
      have hl : raw29907step2Labels = raw29907step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29907step1 raw29907step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw29908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw29908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29908 raw29908Labels = mixedMoment B node1321 node1321Labels := by
  calc
    mixedMoment B raw29908 raw29908Labels = mixedMoment B raw29908step0 raw29908step0Labels := by
      have hz : ∀ j, raw29908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29908step0 = (fun i j => raw29908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29908step0 raw29908; decide +kernel
      have hl : raw29908step0Labels = raw29908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29908 raw29908Labels permutation434 hz
    mixedMoment B raw29908step0 raw29908step0Labels = mixedMoment B raw29908step1 raw29908step1Labels := by
      have ha : raw29908step1 = (fun i j => raw29908step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29908step1 raw29908step0; decide +kernel
      have hl : raw29908step1Labels = raw29908step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29908step0 raw29908step0Labels permutation33 permutation2
    _ = mixedMoment B node1321 node1321Labels := by rfl

def raw29909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29909 raw29909Labels = mixedMoment B node2848 node2848Labels := by
  calc
    mixedMoment B raw29909 raw29909Labels = mixedMoment B raw29909step0 raw29909step0Labels := by
      have ha : raw29909step0 = (fun i j => raw29909 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29909step0 raw29909; decide +kernel
      have hl : raw29909step0Labels = raw29909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29909 raw29909Labels permutation159 permutation2
    _ = mixedMoment B node2848 node2848Labels := by rfl

def raw29910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29910 raw29910Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw29910 raw29910Labels = mixedMoment B raw29910step0 raw29910step0Labels := by
      have hz : ∀ j, raw29910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29910step0 = (fun i j => raw29910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29910step0 raw29910; decide +kernel
      have hl : raw29910step0Labels = raw29910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29910 raw29910Labels permutation434 hz
    _ = mixedMoment B node2885 node2885Labels := by rfl

def raw29911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw29911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29911 raw29911Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw29911 raw29911Labels = mixedMoment B raw29911step0 raw29911step0Labels := by
      have hz : ∀ j, raw29911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29911step0 = (fun i j => raw29911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29911step0 raw29911; decide +kernel
      have hl : raw29911step0Labels = raw29911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29911 raw29911Labels permutation434 hz
    mixedMoment B raw29911step0 raw29911step0Labels = mixedMoment B raw29911step1 raw29911step1Labels := by
      have ha : raw29911step1 = (fun i j => raw29911step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29911step1 raw29911step0; decide +kernel
      have hl : raw29911step1Labels = raw29911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29911step0 raw29911step0Labels permutation36 permutation2
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw29912 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-2, 2, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-2, 2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29912 raw29912Labels = mixedMoment B node3348 node3348Labels := by
  calc
    mixedMoment B raw29912 raw29912Labels = mixedMoment B raw29912step0 raw29912step0Labels := by
      have hz : ∀ j, raw29912 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29912step0 = (fun i j => raw29912 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29912step0 raw29912; decide +kernel
      have hl : raw29912step0Labels = raw29912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29912 raw29912Labels permutation434 hz
    mixedMoment B raw29912step0 raw29912step0Labels = mixedMoment B raw29912step1 raw29912step1Labels := by
      have ha : raw29912step1 = (fun i j => raw29912step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29912step1 raw29912step0; decide +kernel
      have hl : raw29912step1Labels = raw29912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29912step0 raw29912step0Labels permutation36 permutation2
    mixedMoment B raw29912step1 raw29912step1Labels = mixedMoment B raw29912step2 raw29912step2Labels := by
      have ha : raw29912step2 = -raw29912step1 := by apply Matrix.ext; change ∀ i j, raw29912step2 i j = -(raw29912step1 i j); unfold raw29912step2 raw29912step1; decide +kernel
      have hl : raw29912step2Labels = raw29912step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3348 node3348Labels := by rfl

def raw29913 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw29913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw29913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29913 raw29913Labels = mixedMoment B node3345 node3345Labels := by
  calc
    mixedMoment B raw29913 raw29913Labels = mixedMoment B raw29913step0 raw29913step0Labels := by
      have ha : raw29913step0 = (fun i j => raw29913 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29913step0 raw29913; decide +kernel
      have hl : raw29913step0Labels = raw29913Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29913 raw29913Labels permutation170 permutation2
    mixedMoment B raw29913step0 raw29913step0Labels = mixedMoment B raw29913step1 raw29913step1Labels := by
      have ha : raw29913step1 = -raw29913step0 := by apply Matrix.ext; change ∀ i j, raw29913step1 i j = -(raw29913step0 i j); unfold raw29913step1 raw29913step0; decide +kernel
      have hl : raw29913step1Labels = raw29913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3345 node3345Labels := by rfl

def raw29914 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw29914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29914 raw29914Labels = mixedMoment B node2538 node2538Labels := by
  calc
    mixedMoment B raw29914 raw29914Labels = mixedMoment B raw29914step0 raw29914step0Labels := by
      have hz : ∀ j, raw29914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29914step0 = (fun i j => raw29914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29914step0 raw29914; decide +kernel
      have hl : raw29914step0Labels = raw29914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29914 raw29914Labels permutation434 hz
    mixedMoment B raw29914step0 raw29914step0Labels = mixedMoment B raw29914step1 raw29914step1Labels := by
      have ha : raw29914step1 = (fun i j => raw29914step0 (permutation121 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29914step1 raw29914step0; decide +kernel
      have hl : raw29914step1Labels = raw29914step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29914step0 raw29914step0Labels permutation121 permutation2
    _ = mixedMoment B node2538 node2538Labels := by rfl

def raw29915 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29915 raw29915Labels = mixedMoment B node3354 node3354Labels := by
  calc
    mixedMoment B raw29915 raw29915Labels = mixedMoment B raw29915step0 raw29915step0Labels := by
      have hz : ∀ j, raw29915 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29915step0 = (fun i j => raw29915 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29915step0 raw29915; decide +kernel
      have hl : raw29915step0Labels = raw29915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29915 raw29915Labels permutation434 hz
    mixedMoment B raw29915step0 raw29915step0Labels = mixedMoment B raw29915step1 raw29915step1Labels := by
      have ha : raw29915step1 = (fun i j => raw29915step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29915step1 raw29915step0; decide +kernel
      have hl : raw29915step1Labels = raw29915step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29915step0 raw29915step0Labels permutation33 permutation2
    mixedMoment B raw29915step1 raw29915step1Labels = mixedMoment B raw29915step2 raw29915step2Labels := by
      have ha : raw29915step2 = -raw29915step1 := by apply Matrix.ext; change ∀ i j, raw29915step2 i j = -(raw29915step1 i j); unfold raw29915step2 raw29915step1; decide +kernel
      have hl : raw29915step2Labels = raw29915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3354 node3354Labels := by rfl

def raw29916 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29916 raw29916Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw29916 raw29916Labels = mixedMoment B raw29916step0 raw29916step0Labels := by
      have hz : ∀ j, raw29916 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29916step0 = (fun i j => raw29916 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29916step0 raw29916; decide +kernel
      have hl : raw29916step0Labels = raw29916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29916 raw29916Labels permutation434 hz
    mixedMoment B raw29916step0 raw29916step0Labels = mixedMoment B raw29916step1 raw29916step1Labels := by
      have ha : raw29916step1 = (fun i j => raw29916step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29916step1 raw29916step0; decide +kernel
      have hl : raw29916step1Labels = raw29916step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29916step0 raw29916step0Labels permutation38 permutation4
    mixedMoment B raw29916step1 raw29916step1Labels = mixedMoment B raw29916step2 raw29916step2Labels := by
      have ha : raw29916step2 = -raw29916step1 := by apply Matrix.ext; change ∀ i j, raw29916step2 i j = -(raw29916step1 i j); unfold raw29916step2 raw29916step1; decide +kernel
      have hl : raw29916step2Labels = raw29916step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2048 node2048Labels := by rfl

def raw29917 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 2, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29917step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29917 raw29917Labels = mixedMoment B node3386 node3386Labels := by
  calc
    mixedMoment B raw29917 raw29917Labels = mixedMoment B raw29917step0 raw29917step0Labels := by
      have hz : ∀ j, raw29917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29917step0 = (fun i j => raw29917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29917step0 raw29917; decide +kernel
      have hl : raw29917step0Labels = raw29917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29917 raw29917Labels permutation434 hz
    mixedMoment B raw29917step0 raw29917step0Labels = mixedMoment B raw29917step1 raw29917step1Labels := by
      have ha : raw29917step1 = (fun i j => raw29917step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29917step1 raw29917step0; decide +kernel
      have hl : raw29917step1Labels = raw29917step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29917step0 raw29917step0Labels permutation38 permutation4
    mixedMoment B raw29917step1 raw29917step1Labels = mixedMoment B raw29917step2 raw29917step2Labels := by
      have ha : raw29917step2 = -raw29917step1 := by apply Matrix.ext; change ∀ i j, raw29917step2 i j = -(raw29917step1 i j); unfold raw29917step2 raw29917step1; decide +kernel
      have hl : raw29917step2Labels = raw29917step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3386 node3386Labels := by rfl

def raw29918 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29918 raw29918Labels = mixedMoment B node3491 node3491Labels := by
  calc
    mixedMoment B raw29918 raw29918Labels = mixedMoment B raw29918step0 raw29918step0Labels := by
      have ha : raw29918step0 = (fun i j => raw29918 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29918step0 raw29918; decide +kernel
      have hl : raw29918step0Labels = raw29918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29918 raw29918Labels permutation182 permutation4
    mixedMoment B raw29918step0 raw29918step0Labels = mixedMoment B raw29918step1 raw29918step1Labels := by
      have ha : raw29918step1 = -raw29918step0 := by apply Matrix.ext; change ∀ i j, raw29918step1 i j = -(raw29918step0 i j); unfold raw29918step1 raw29918step0; decide +kernel
      have hl : raw29918step1Labels = raw29918step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3491 node3491Labels := by rfl

def raw29919 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29919 raw29919Labels = mixedMoment B node2838 node2838Labels := by
  calc
    mixedMoment B raw29919 raw29919Labels = mixedMoment B raw29919step0 raw29919step0Labels := by
      have hz : ∀ j, raw29919 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29919step0 = (fun i j => raw29919 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29919step0 raw29919; decide +kernel
      have hl : raw29919step0Labels = raw29919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29919 raw29919Labels permutation434 hz
    mixedMoment B raw29919step0 raw29919step0Labels = mixedMoment B raw29919step1 raw29919step1Labels := by
      have ha : raw29919step1 = (fun i j => raw29919step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29919step1 raw29919step0; decide +kernel
      have hl : raw29919step1Labels = raw29919step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29919step0 raw29919step0Labels permutation57 permutation2
    mixedMoment B raw29919step1 raw29919step1Labels = mixedMoment B raw29919step2 raw29919step2Labels := by
      have ha : raw29919step2 = -raw29919step1 := by apply Matrix.ext; change ∀ i j, raw29919step2 i j = -(raw29919step1 i j); unfold raw29919step2 raw29919step1; decide +kernel
      have hl : raw29919step2Labels = raw29919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2838 node2838Labels := by rfl

def raw29920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29920 raw29920Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw29920 raw29920Labels = mixedMoment B raw29920step0 raw29920step0Labels := by
      have hz : ∀ j, raw29920 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29920step0 = (fun i j => raw29920 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29920step0 raw29920; decide +kernel
      have hl : raw29920step0Labels = raw29920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29920 raw29920Labels permutation434 hz
    mixedMoment B raw29920step0 raw29920step0Labels = mixedMoment B raw29920step1 raw29920step1Labels := by
      have ha : raw29920step1 = (fun i j => raw29920step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29920step1 raw29920step0; decide +kernel
      have hl : raw29920step1Labels = raw29920step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29920step0 raw29920step0Labels permutation38 permutation2
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw29921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29921 raw29921Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw29921 raw29921Labels = mixedMoment B raw29921step0 raw29921step0Labels := by
      have hz : ∀ j, raw29921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29921step0 = (fun i j => raw29921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29921step0 raw29921; decide +kernel
      have hl : raw29921step0Labels = raw29921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29921 raw29921Labels permutation434 hz
    mixedMoment B raw29921step0 raw29921step0Labels = mixedMoment B raw29921step1 raw29921step1Labels := by
      have ha : raw29921step1 = (fun i j => raw29921step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29921step1 raw29921step0; decide +kernel
      have hl : raw29921step1Labels = raw29921step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29921step0 raw29921step0Labels permutation38 permutation2
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw29922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29922 raw29922Labels = mixedMoment B node2621 node2621Labels := by
  calc
    mixedMoment B raw29922 raw29922Labels = mixedMoment B raw29922step0 raw29922step0Labels := by
      have hz : ∀ j, raw29922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29922step0 = (fun i j => raw29922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29922step0 raw29922; decide +kernel
      have hl : raw29922step0Labels = raw29922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29922 raw29922Labels permutation434 hz
    _ = mixedMoment B node2621 node2621Labels := by rfl

def raw29923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29923 raw29923Labels = mixedMoment B node2439 node2439Labels := by
  calc
    mixedMoment B raw29923 raw29923Labels = mixedMoment B raw29923step0 raw29923step0Labels := by
      have ha : raw29923step0 = (fun i j => raw29923 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29923step0 raw29923; decide +kernel
      have hl : raw29923step0Labels = raw29923Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29923 raw29923Labels permutation176 permutation2
    _ = mixedMoment B node2439 node2439Labels := by rfl

def raw29924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw29924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29924 raw29924Labels = mixedMoment B node2442 node2442Labels := by
  calc
    mixedMoment B raw29924 raw29924Labels = mixedMoment B raw29924step0 raw29924step0Labels := by
      have hz : ∀ j, raw29924 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29924step0 = (fun i j => raw29924 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29924step0 raw29924; decide +kernel
      have hl : raw29924step0Labels = raw29924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29924 raw29924Labels permutation434 hz
    mixedMoment B raw29924step0 raw29924step0Labels = mixedMoment B raw29924step1 raw29924step1Labels := by
      have ha : raw29924step1 = (fun i j => raw29924step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29924step1 raw29924step0; decide +kernel
      have hl : raw29924step1Labels = raw29924step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29924step0 raw29924step0Labels permutation39 permutation2
    _ = mixedMoment B node2442 node2442Labels := by rfl

def raw29925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw29925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw29925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29925 raw29925Labels = mixedMoment B node2442 node2442Labels := by
  calc
    mixedMoment B raw29925 raw29925Labels = mixedMoment B raw29925step0 raw29925step0Labels := by
      have hz : ∀ j, raw29925 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29925step0 = (fun i j => raw29925 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29925step0 raw29925; decide +kernel
      have hl : raw29925step0Labels = raw29925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29925 raw29925Labels permutation434 hz
    mixedMoment B raw29925step0 raw29925step0Labels = mixedMoment B raw29925step1 raw29925step1Labels := by
      have ha : raw29925step1 = (fun i j => raw29925step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29925step1 raw29925step0; decide +kernel
      have hl : raw29925step1Labels = raw29925step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29925step0 raw29925step0Labels permutation38 permutation2
    _ = mixedMoment B node2442 node2442Labels := by rfl

def raw29926 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]
def raw29926Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29926step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw29926step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29926step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw29926step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29926 raw29926Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw29926 raw29926Labels = mixedMoment B raw29926step0 raw29926step0Labels := by
      have hz : ∀ j, raw29926 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29926step0 = (fun i j => raw29926 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29926step0 raw29926; decide +kernel
      have hl : raw29926step0Labels = raw29926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29926 raw29926Labels permutation434 hz
    mixedMoment B raw29926step0 raw29926step0Labels = mixedMoment B raw29926step1 raw29926step1Labels := by
      have ha : raw29926step1 = (fun i j => raw29926step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29926step1 raw29926step0; decide +kernel
      have hl : raw29926step1Labels = raw29926step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29926step0 raw29926step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw29927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29927step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29927 raw29927Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw29927 raw29927Labels = mixedMoment B raw29927step0 raw29927step0Labels := by
      have hz : ∀ j, raw29927 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29927step0 = (fun i j => raw29927 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29927step0 raw29927; decide +kernel
      have hl : raw29927step0Labels = raw29927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29927 raw29927Labels permutation434 hz
    mixedMoment B raw29927step0 raw29927step0Labels = mixedMoment B raw29927step1 raw29927step1Labels := by
      have ha : raw29927step1 = (fun i j => raw29927step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29927step1 raw29927step0; decide +kernel
      have hl : raw29927step1Labels = raw29927step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29927step0 raw29927step0Labels permutation56 permutation2
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw29928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29928 raw29928Labels = mixedMoment B node2868 node2868Labels := by
  calc
    mixedMoment B raw29928 raw29928Labels = mixedMoment B raw29928step0 raw29928step0Labels := by
      have hz : ∀ j, raw29928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29928step0 = (fun i j => raw29928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29928step0 raw29928; decide +kernel
      have hl : raw29928step0Labels = raw29928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29928 raw29928Labels permutation434 hz
    _ = mixedMoment B node2868 node2868Labels := by rfl

def raw29929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29929 raw29929Labels = mixedMoment B node2818 node2818Labels := by
  calc
    mixedMoment B raw29929 raw29929Labels = mixedMoment B raw29929step0 raw29929step0Labels := by
      have hz : ∀ j, raw29929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29929step0 = (fun i j => raw29929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29929step0 raw29929; decide +kernel
      have hl : raw29929step0Labels = raw29929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29929 raw29929Labels permutation434 hz
    _ = mixedMoment B node2818 node2818Labels := by rfl

def raw29930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29930 raw29930Labels = mixedMoment B node2799 node2799Labels := by
  calc
    _ = mixedMoment B node2799 node2799Labels := by rfl

def raw29931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw29931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29931 raw29931Labels = mixedMoment B node2802 node2802Labels := by
  calc
    mixedMoment B raw29931 raw29931Labels = mixedMoment B raw29931step0 raw29931step0Labels := by
      have hz : ∀ j, raw29931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29931step0 = (fun i j => raw29931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29931step0 raw29931; decide +kernel
      have hl : raw29931step0Labels = raw29931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29931 raw29931Labels permutation434 hz
    mixedMoment B raw29931step0 raw29931step0Labels = mixedMoment B raw29931step1 raw29931step1Labels := by
      have ha : raw29931step1 = (fun i j => raw29931step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29931step1 raw29931step0; decide +kernel
      have hl : raw29931step1Labels = raw29931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29931step0 raw29931step0Labels permutation33 permutation2
    _ = mixedMoment B node2802 node2802Labels := by rfl

def raw29932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw29932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29932 raw29932Labels = mixedMoment B node2802 node2802Labels := by
  calc
    mixedMoment B raw29932 raw29932Labels = mixedMoment B raw29932step0 raw29932step0Labels := by
      have hz : ∀ j, raw29932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29932step0 = (fun i j => raw29932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29932step0 raw29932; decide +kernel
      have hl : raw29932step0Labels = raw29932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29932 raw29932Labels permutation434 hz
    _ = mixedMoment B node2802 node2802Labels := by rfl

def raw29933 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw29933Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29933step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw29933step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29933step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw29933step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29933 raw29933Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw29933 raw29933Labels = mixedMoment B raw29933step0 raw29933step0Labels := by
      have hz : ∀ j, raw29933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29933step0 = (fun i j => raw29933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29933step0 raw29933; decide +kernel
      have hl : raw29933step0Labels = raw29933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29933 raw29933Labels permutation434 hz
    mixedMoment B raw29933step0 raw29933step0Labels = mixedMoment B raw29933step1 raw29933step1Labels := by
      have ha : raw29933step1 = (fun i j => raw29933step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29933step1 raw29933step0; decide +kernel
      have hl : raw29933step1Labels = raw29933step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29933step0 raw29933step0Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw29934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29934 raw29934Labels = mixedMoment B node1322 node1322Labels := by
  calc
    mixedMoment B raw29934 raw29934Labels = mixedMoment B raw29934step0 raw29934step0Labels := by
      have hz : ∀ j, raw29934 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29934step0 = (fun i j => raw29934 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29934step0 raw29934; decide +kernel
      have hl : raw29934step0Labels = raw29934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29934 raw29934Labels permutation434 hz
    _ = mixedMoment B node1322 node1322Labels := by rfl

def raw29935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29935 raw29935Labels = mixedMoment B node2849 node2849Labels := by
  calc
    mixedMoment B raw29935 raw29935Labels = mixedMoment B raw29935step0 raw29935step0Labels := by
      have ha : raw29935step0 = (fun i j => raw29935 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29935step0 raw29935; decide +kernel
      have hl : raw29935step0Labels = raw29935Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29935 raw29935Labels permutation158 permutation2
    _ = mixedMoment B node2849 node2849Labels := by rfl

def raw29936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29936 raw29936Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw29936 raw29936Labels = mixedMoment B raw29936step0 raw29936step0Labels := by
      have hz : ∀ j, raw29936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29936step0 = (fun i j => raw29936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29936step0 raw29936; decide +kernel
      have hl : raw29936step0Labels = raw29936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29936 raw29936Labels permutation434 hz
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw29937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw29937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29937 raw29937Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw29937 raw29937Labels = mixedMoment B raw29937step0 raw29937step0Labels := by
      have hz : ∀ j, raw29937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29937step0 = (fun i j => raw29937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29937step0 raw29937; decide +kernel
      have hl : raw29937step0Labels = raw29937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29937 raw29937Labels permutation434 hz
    mixedMoment B raw29937step0 raw29937step0Labels = mixedMoment B raw29937step1 raw29937step1Labels := by
      have ha : raw29937step1 = (fun i j => raw29937step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29937step1 raw29937step0; decide +kernel
      have hl : raw29937step1Labels = raw29937step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29937step0 raw29937step0Labels permutation33 permutation2
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw29938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 1, -3], ![2, -2, 0]]
def raw29938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw29938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29938 raw29938Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw29938 raw29938Labels = mixedMoment B raw29938step0 raw29938step0Labels := by
      have hz : ∀ j, raw29938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29938step0 = (fun i j => raw29938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29938step0 raw29938; decide +kernel
      have hl : raw29938step0Labels = raw29938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29938 raw29938Labels permutation434 hz
    mixedMoment B raw29938step0 raw29938step0Labels = mixedMoment B raw29938step1 raw29938step1Labels := by
      have hz : ∀ j, raw29938step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29938step1 = (fun i j => raw29938step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29938step1 raw29938step0; decide +kernel
      have hl : raw29938step1Labels = raw29938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29938step0 raw29938step0Labels permutation80 hz
    mixedMoment B raw29938step1 raw29938step1Labels = mixedMoment B raw29938step2 raw29938step2Labels := by
      have ha : raw29938step2 = (fun i j => raw29938step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29938step2 raw29938step1; decide +kernel
      have hl : raw29938step2Labels = raw29938step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29938step1 raw29938step1Labels permutation24 permutation2
    mixedMoment B raw29938step2 raw29938step2Labels = mixedMoment B raw29938step3 raw29938step3Labels := by
      have ha : raw29938step3 = -raw29938step2 := by apply Matrix.ext; change ∀ i j, raw29938step3 i j = -(raw29938step2 i j); unfold raw29938step3 raw29938step2; decide +kernel
      have hl : raw29938step3Labels = raw29938step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3397 node3397Labels := by rfl

def raw29939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 1, -3], ![2, -2, 0]]
def raw29939step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw29939step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29939 raw29939Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw29939 raw29939Labels = mixedMoment B raw29939step0 raw29939step0Labels := by
      have hz : ∀ j, raw29939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29939step0 = (fun i j => raw29939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29939step0 raw29939; decide +kernel
      have hl : raw29939step0Labels = raw29939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29939 raw29939Labels permutation434 hz
    mixedMoment B raw29939step0 raw29939step0Labels = mixedMoment B raw29939step1 raw29939step1Labels := by
      have hz : ∀ j, raw29939step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29939step1 = (fun i j => raw29939step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29939step1 raw29939step0; decide +kernel
      have hl : raw29939step1Labels = raw29939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29939step0 raw29939step0Labels permutation80 hz
    mixedMoment B raw29939step1 raw29939step1Labels = mixedMoment B raw29939step2 raw29939step2Labels := by
      have ha : raw29939step2 = (fun i j => raw29939step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29939step2 raw29939step1; decide +kernel
      have hl : raw29939step2Labels = raw29939step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29939step1 raw29939step1Labels permutation9 permutation2
    _ = mixedMoment B node2888 node2888Labels := by rfl

def raw29940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29940step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29940 raw29940Labels = mixedMoment B node2812 node2812Labels := by
  calc
    mixedMoment B raw29940 raw29940Labels = mixedMoment B raw29940step0 raw29940step0Labels := by
      have hz : ∀ j, raw29940 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29940step0 = (fun i j => raw29940 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29940step0 raw29940; decide +kernel
      have hl : raw29940step0Labels = raw29940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29940 raw29940Labels permutation434 hz
    mixedMoment B raw29940step0 raw29940step0Labels = mixedMoment B raw29940step1 raw29940step1Labels := by
      have ha : raw29940step1 = (fun i j => raw29940step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29940step1 raw29940step0; decide +kernel
      have hl : raw29940step1Labels = raw29940step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29940step0 raw29940step0Labels permutation33 permutation2
    _ = mixedMoment B node2812 node2812Labels := by rfl

def raw29941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29941step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29941 raw29941Labels = mixedMoment B node2812 node2812Labels := by
  calc
    mixedMoment B raw29941 raw29941Labels = mixedMoment B raw29941step0 raw29941step0Labels := by
      have hz : ∀ j, raw29941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29941step0 = (fun i j => raw29941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29941step0 raw29941; decide +kernel
      have hl : raw29941step0Labels = raw29941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29941 raw29941Labels permutation346 hz
    mixedMoment B raw29941step0 raw29941step0Labels = mixedMoment B raw29941step1 raw29941step1Labels := by
      have ha : raw29941step1 = (fun i j => raw29941step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29941step1 raw29941step0; decide +kernel
      have hl : raw29941step1Labels = raw29941step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29941step0 raw29941step0Labels permutation33 permutation2
    _ = mixedMoment B node2812 node2812Labels := by rfl

def raw29942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw29942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw29942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![3, 0, -3], ![2, -2, 0]]
def raw29942step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw29942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29942step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29942 raw29942Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw29942 raw29942Labels = mixedMoment B raw29942step0 raw29942step0Labels := by
      have hz : ∀ j, raw29942 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29942step0 = (fun i j => raw29942 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29942step0 raw29942; decide +kernel
      have hl : raw29942step0Labels = raw29942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29942 raw29942Labels permutation434 hz
    mixedMoment B raw29942step0 raw29942step0Labels = mixedMoment B raw29942step1 raw29942step1Labels := by
      have hz : ∀ j, raw29942step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29942step1 = (fun i j => raw29942step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29942step1 raw29942step0; decide +kernel
      have hl : raw29942step1Labels = raw29942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29942step0 raw29942step0Labels permutation80 hz
    mixedMoment B raw29942step1 raw29942step1Labels = mixedMoment B raw29942step2 raw29942step2Labels := by
      have ha : raw29942step2 = (fun i j => raw29942step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29942step2 raw29942step1; decide +kernel
      have hl : raw29942step2Labels = raw29942step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29942step1 raw29942step1Labels permutation25 permutation2
    mixedMoment B raw29942step2 raw29942step2Labels = mixedMoment B raw29942step3 raw29942step3Labels := by
      have ha : raw29942step3 = -raw29942step2 := by apply Matrix.ext; change ∀ i j, raw29942step3 i j = -(raw29942step2 i j); unfold raw29942step3 raw29942step2; decide +kernel
      have hl : raw29942step3Labels = raw29942step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1819 node1819Labels := by rfl

def raw29943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw29943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw29943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw29943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29943 raw29943Labels = mixedMoment B node2821 node2821Labels := by
  calc
    mixedMoment B raw29943 raw29943Labels = mixedMoment B raw29943step0 raw29943step0Labels := by
      have hz : ∀ j, raw29943 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29943step0 = (fun i j => raw29943 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29943step0 raw29943; decide +kernel
      have hl : raw29943step0Labels = raw29943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29943 raw29943Labels permutation434 hz
    mixedMoment B raw29943step0 raw29943step0Labels = mixedMoment B raw29943step1 raw29943step1Labels := by
      have hz : ∀ j, raw29943step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29943step1 = (fun i j => raw29943step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29943step1 raw29943step0; decide +kernel
      have hl : raw29943step1Labels = raw29943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29943step0 raw29943step0Labels permutation80 hz
    _ = mixedMoment B node2821 node2821Labels := by rfl

def raw29944 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![0, 0], ![3, -3], ![0, 0]]
def raw29944Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![0, 0], ![3, -3]]
def raw29944step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]
def raw29944step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]
def raw29944step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw29944step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29944step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29944 raw29944Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw29944 raw29944Labels = mixedMoment B raw29944step0 raw29944step0Labels := by
      have hz : ∀ j, raw29944 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw29944step0 = (fun i j => raw29944 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw29944step0 raw29944; decide +kernel
      have hl : raw29944step0Labels = raw29944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29944 raw29944Labels permutation590 hz
    mixedMoment B raw29944step0 raw29944step0Labels = mixedMoment B raw29944step1 raw29944step1Labels := by
      have hz : ∀ j, raw29944step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29944step1 = (fun i j => raw29944step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29944step1 raw29944step0; decide +kernel
      have hl : raw29944step1Labels = raw29944step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29944step0 raw29944step0Labels permutation104 hz
    mixedMoment B raw29944step1 raw29944step1Labels = mixedMoment B raw29944step2 raw29944step2Labels := by
      have hz : ∀ j, raw29944step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29944step2 = (fun i j => raw29944step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29944step2 raw29944step1; decide +kernel
      have hl : raw29944step2Labels = raw29944step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29944step1 raw29944step1Labels permutation20 hz
    mixedMoment B raw29944step2 raw29944step2Labels = mixedMoment B raw29944step3 raw29944step3Labels := by
      have ha : raw29944step3 = (fun i j => raw29944step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29944step3 raw29944step2; decide +kernel
      have hl : raw29944step3Labels = raw29944step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29944step2 raw29944step2Labels permutation6 permutation0
    mixedMoment B raw29944step3 raw29944step3Labels = mixedMoment B raw29944step4 raw29944step4Labels := by
      have ha : raw29944step4 = -raw29944step3 := by apply Matrix.ext; change ∀ i j, raw29944step4 i j = -(raw29944step3 i j); unfold raw29944step4 raw29944step3; decide +kernel
      have hl : raw29944step4Labels = raw29944step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw29945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29945step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29945step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29945step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29945 raw29945Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw29945 raw29945Labels = mixedMoment B raw29945step0 raw29945step0Labels := by
      have hz : ∀ j, raw29945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29945step0 = (fun i j => raw29945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29945step0 raw29945; decide +kernel
      have hl : raw29945step0Labels = raw29945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29945 raw29945Labels permutation434 hz
    mixedMoment B raw29945step0 raw29945step0Labels = mixedMoment B raw29945step1 raw29945step1Labels := by
      have hz : ∀ j, raw29945step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29945step1 = (fun i j => raw29945step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29945step1 raw29945step0; decide +kernel
      have hl : raw29945step1Labels = raw29945step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29945step0 raw29945step0Labels permutation80 hz
    mixedMoment B raw29945step1 raw29945step1Labels = mixedMoment B raw29945step2 raw29945step2Labels := by
      have ha : raw29945step2 = (fun i j => raw29945step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29945step2 raw29945step1; decide +kernel
      have hl : raw29945step2Labels = raw29945step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29945step1 raw29945step1Labels permutation9 permutation3
    mixedMoment B raw29945step2 raw29945step2Labels = mixedMoment B raw29945step3 raw29945step3Labels := by
      have ha : raw29945step3 = raw29945step2 := by apply Matrix.ext; unfold raw29945step3 raw29945step2; decide +kernel
      have hl : raw29945step2Labels = labelEmbedding6 ∘ raw29945step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29945step2 raw29945step2Labels raw29945step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw29946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29946 raw29946Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw29946 raw29946Labels = mixedMoment B raw29946step0 raw29946step0Labels := by
      have hz : ∀ j, raw29946 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29946step0 = (fun i j => raw29946 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29946step0 raw29946; decide +kernel
      have hl : raw29946step0Labels = raw29946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29946 raw29946Labels permutation434 hz
    mixedMoment B raw29946step0 raw29946step0Labels = mixedMoment B raw29946step1 raw29946step1Labels := by
      have ha : raw29946step1 = (fun i j => raw29946step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29946step1 raw29946step0; decide +kernel
      have hl : raw29946step1Labels = raw29946step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29946step0 raw29946step0Labels permutation38 permutation2
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw29947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29947 raw29947Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw29947 raw29947Labels = mixedMoment B raw29947step0 raw29947step0Labels := by
      have hz : ∀ j, raw29947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29947step0 = (fun i j => raw29947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29947step0 raw29947; decide +kernel
      have hl : raw29947step0Labels = raw29947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29947 raw29947Labels permutation346 hz
    mixedMoment B raw29947step0 raw29947step0Labels = mixedMoment B raw29947step1 raw29947step1Labels := by
      have ha : raw29947step1 = (fun i j => raw29947step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29947step1 raw29947step0; decide +kernel
      have hl : raw29947step1Labels = raw29947step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29947step0 raw29947step0Labels permutation38 permutation2
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw29948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw29948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw29948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29948step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29948 raw29948Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw29948 raw29948Labels = mixedMoment B raw29948step0 raw29948step0Labels := by
      have hz : ∀ j, raw29948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29948step0 = (fun i j => raw29948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29948step0 raw29948; decide +kernel
      have hl : raw29948step0Labels = raw29948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29948 raw29948Labels permutation434 hz
    mixedMoment B raw29948step0 raw29948step0Labels = mixedMoment B raw29948step1 raw29948step1Labels := by
      have hz : ∀ j, raw29948step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29948step1 = (fun i j => raw29948step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29948step1 raw29948step0; decide +kernel
      have hl : raw29948step1Labels = raw29948step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29948step0 raw29948step0Labels permutation80 hz
    mixedMoment B raw29948step1 raw29948step1Labels = mixedMoment B raw29948step2 raw29948step2Labels := by
      have ha : raw29948step2 = (fun i j => raw29948step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29948step2 raw29948step1; decide +kernel
      have hl : raw29948step2Labels = raw29948step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29948step1 raw29948step1Labels permutation9 permutation2
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw29949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29949step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29949step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29949 raw29949Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw29949 raw29949Labels = mixedMoment B raw29949step0 raw29949step0Labels := by
      have hz : ∀ j, raw29949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29949step0 = (fun i j => raw29949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29949step0 raw29949; decide +kernel
      have hl : raw29949step0Labels = raw29949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29949 raw29949Labels permutation434 hz
    mixedMoment B raw29949step0 raw29949step0Labels = mixedMoment B raw29949step1 raw29949step1Labels := by
      have ha : raw29949step1 = (fun i j => raw29949step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29949step1 raw29949step0; decide +kernel
      have hl : raw29949step1Labels = raw29949step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29949step0 raw29949step0Labels permutation33 permutation3
    mixedMoment B raw29949step1 raw29949step1Labels = mixedMoment B raw29949step2 raw29949step2Labels := by
      have ha : raw29949step2 = raw29949step1 := by apply Matrix.ext; unfold raw29949step2 raw29949step1; decide +kernel
      have hl : raw29949step1Labels = labelEmbedding6 ∘ raw29949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29949step1 raw29949step1Labels raw29949step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

def raw29950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29950 raw29950Labels = mixedMoment B node4983 node4983Labels := by
  calc
    mixedMoment B raw29950 raw29950Labels = mixedMoment B raw29950step0 raw29950step0Labels := by
      have hz : ∀ j, raw29950 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29950step0 = (fun i j => raw29950 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29950step0 raw29950; decide +kernel
      have hl : raw29950step0Labels = raw29950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29950 raw29950Labels permutation434 hz
    _ = mixedMoment B node4983 node4983Labels := by rfl

def raw29951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29951 raw29951Labels = mixedMoment B node5119 node5119Labels := by
  calc
    mixedMoment B raw29951 raw29951Labels = mixedMoment B raw29951step0 raw29951step0Labels := by
      have ha : raw29951step0 = (fun i j => raw29951 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29951step0 raw29951; decide +kernel
      have hl : raw29951step0Labels = raw29951Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29951 raw29951Labels permutation200 permutation2
    _ = mixedMoment B node5119 node5119Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
