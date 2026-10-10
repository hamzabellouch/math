import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7936 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7936step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7936 raw7936Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw7936 raw7936Labels = mixedMoment B raw7936step0 raw7936step0Labels := by
      have hz : ∀ j, raw7936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7936step0 = (fun i j => raw7936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7936step0 raw7936; decide +kernel
      have hl : raw7936step0Labels = raw7936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7936 raw7936Labels permutation434 hz
    mixedMoment B raw7936step0 raw7936step0Labels = mixedMoment B raw7936step1 raw7936step1Labels := by
      have hz : ∀ j, raw7936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7936step1 = (fun i j => raw7936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7936step1 raw7936step0; decide +kernel
      have hl : raw7936step1Labels = raw7936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7936step0 raw7936step0Labels permutation80 hz
    mixedMoment B raw7936step1 raw7936step1Labels = mixedMoment B raw7936step2 raw7936step2Labels := by
      have ha : raw7936step2 = (fun i j => raw7936step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7936step2 raw7936step1; decide +kernel
      have hl : raw7936step2Labels = raw7936step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7936step1 raw7936step1Labels permutation8 permutation6
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw7937 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7937 raw7937Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw7937 raw7937Labels = mixedMoment B raw7937step0 raw7937step0Labels := by
      have hz : ∀ j, raw7937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7937step0 = (fun i j => raw7937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7937step0 raw7937; decide +kernel
      have hl : raw7937step0Labels = raw7937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7937 raw7937Labels permutation346 hz
    mixedMoment B raw7937step0 raw7937step0Labels = mixedMoment B raw7937step1 raw7937step1Labels := by
      have ha : raw7937step1 = (fun i j => raw7937step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7937step1 raw7937step0; decide +kernel
      have hl : raw7937step1Labels = raw7937step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7937step0 raw7937step0Labels permutation32 permutation6
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw7938 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7938step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7938 raw7938Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw7938 raw7938Labels = mixedMoment B raw7938step0 raw7938step0Labels := by
      have hz : ∀ j, raw7938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7938step0 = (fun i j => raw7938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7938step0 raw7938; decide +kernel
      have hl : raw7938step0Labels = raw7938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7938 raw7938Labels permutation346 hz
    mixedMoment B raw7938step0 raw7938step0Labels = mixedMoment B raw7938step1 raw7938step1Labels := by
      have hz : ∀ j, raw7938step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7938step1 = (fun i j => raw7938step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7938step1 raw7938step0; decide +kernel
      have hl : raw7938step1Labels = raw7938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7938step0 raw7938step0Labels permutation56 hz
    mixedMoment B raw7938step1 raw7938step1Labels = mixedMoment B raw7938step2 raw7938step2Labels := by
      have ha : raw7938step2 = (fun i j => raw7938step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7938step2 raw7938step1; decide +kernel
      have hl : raw7938step2Labels = raw7938step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7938step1 raw7938step1Labels permutation8 permutation6
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw7939 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7939Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7939step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7939step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7939 raw7939Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw7939 raw7939Labels = mixedMoment B raw7939step0 raw7939step0Labels := by
      have hz : ∀ j, raw7939 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7939step0 = (fun i j => raw7939 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7939step0 raw7939; decide +kernel
      have hl : raw7939step0Labels = raw7939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7939 raw7939Labels permutation265 hz
    mixedMoment B raw7939step0 raw7939step0Labels = mixedMoment B raw7939step1 raw7939step1Labels := by
      have ha : raw7939step1 = (fun i j => raw7939step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7939step1 raw7939step0; decide +kernel
      have hl : raw7939step1Labels = raw7939step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7939step0 raw7939step0Labels permutation32 permutation6
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw7940 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7940Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7940step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7940step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7940 raw7940Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw7940 raw7940Labels = mixedMoment B raw7940step0 raw7940step0Labels := by
      have hz : ∀ j, raw7940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7940step0 = (fun i j => raw7940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7940step0 raw7940; decide +kernel
      have hl : raw7940step0Labels = raw7940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7940 raw7940Labels permutation346 hz
    mixedMoment B raw7940step0 raw7940step0Labels = mixedMoment B raw7940step1 raw7940step1Labels := by
      have hz : ∀ j, raw7940step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7940step1 = (fun i j => raw7940step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7940step1 raw7940step0; decide +kernel
      have hl : raw7940step1Labels = raw7940step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7940step0 raw7940step0Labels permutation56 hz
    mixedMoment B raw7940step1 raw7940step1Labels = mixedMoment B raw7940step2 raw7940step2Labels := by
      have ha : raw7940step2 = (fun i j => raw7940step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7940step2 raw7940step1; decide +kernel
      have hl : raw7940step2Labels = raw7940step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7940step1 raw7940step1Labels permutation8 permutation6
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw7941 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7941Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7941step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7941 raw7941Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw7941 raw7941Labels = mixedMoment B raw7941step0 raw7941step0Labels := by
      have hz : ∀ j, raw7941 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7941step0 = (fun i j => raw7941 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7941step0 raw7941; decide +kernel
      have hl : raw7941step0Labels = raw7941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7941 raw7941Labels permutation265 hz
    mixedMoment B raw7941step0 raw7941step0Labels = mixedMoment B raw7941step1 raw7941step1Labels := by
      have ha : raw7941step1 = (fun i j => raw7941step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7941step1 raw7941step0; decide +kernel
      have hl : raw7941step1Labels = raw7941step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7941step0 raw7941step0Labels permutation32 permutation6
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw7942 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7942Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7942step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7942step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7942step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![0, -2, 2]]
def raw7942step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7942step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7942step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7942 raw7942Labels = mixedMoment B node2786 node2786Labels := by
  calc
    mixedMoment B raw7942 raw7942Labels = mixedMoment B raw7942step0 raw7942step0Labels := by
      have hz : ∀ j, raw7942 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7942step0 = (fun i j => raw7942 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7942step0 raw7942; decide +kernel
      have hl : raw7942step0Labels = raw7942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7942 raw7942Labels permutation434 hz
    mixedMoment B raw7942step0 raw7942step0Labels = mixedMoment B raw7942step1 raw7942step1Labels := by
      have hz : ∀ j, raw7942step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7942step1 = (fun i j => raw7942step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7942step1 raw7942step0; decide +kernel
      have hl : raw7942step1Labels = raw7942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7942step0 raw7942step0Labels permutation80 hz
    mixedMoment B raw7942step1 raw7942step1Labels = mixedMoment B raw7942step2 raw7942step2Labels := by
      have hz : ∀ j, raw7942step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7942step2 = (fun i j => raw7942step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7942step2 raw7942step1; decide +kernel
      have hl : raw7942step2Labels = raw7942step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7942step1 raw7942step1Labels permutation14 hz
    mixedMoment B raw7942step2 raw7942step2Labels = mixedMoment B raw7942step3 raw7942step3Labels := by
      have ha : raw7942step3 = (fun i j => raw7942step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7942step3 raw7942step2; decide +kernel
      have hl : raw7942step3Labels = raw7942step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7942step2 raw7942step2Labels permutation2 permutation6
    _ = mixedMoment B node2786 node2786Labels := by rfl

def raw7943 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7943step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7943 raw7943Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw7943 raw7943Labels = mixedMoment B raw7943step0 raw7943step0Labels := by
      have hz : ∀ j, raw7943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7943step0 = (fun i j => raw7943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7943step0 raw7943; decide +kernel
      have hl : raw7943step0Labels = raw7943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7943 raw7943Labels permutation346 hz
    mixedMoment B raw7943step0 raw7943step0Labels = mixedMoment B raw7943step1 raw7943step1Labels := by
      have hz : ∀ j, raw7943step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7943step1 = (fun i j => raw7943step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7943step1 raw7943step0; decide +kernel
      have hl : raw7943step1Labels = raw7943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7943step0 raw7943step0Labels permutation56 hz
    mixedMoment B raw7943step1 raw7943step1Labels = mixedMoment B raw7943step2 raw7943step2Labels := by
      have ha : raw7943step2 = (fun i j => raw7943step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7943step2 raw7943step1; decide +kernel
      have hl : raw7943step2Labels = raw7943step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7943step1 raw7943step1Labels permutation8 permutation6
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw7944 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7944step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7944 raw7944Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw7944 raw7944Labels = mixedMoment B raw7944step0 raw7944step0Labels := by
      have hz : ∀ j, raw7944 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7944step0 = (fun i j => raw7944 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7944step0 raw7944; decide +kernel
      have hl : raw7944step0Labels = raw7944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7944 raw7944Labels permutation265 hz
    mixedMoment B raw7944step0 raw7944step0Labels = mixedMoment B raw7944step1 raw7944step1Labels := by
      have ha : raw7944step1 = (fun i j => raw7944step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7944step1 raw7944step0; decide +kernel
      have hl : raw7944step1Labels = raw7944step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7944step0 raw7944step0Labels permutation38 permutation7
    mixedMoment B raw7944step1 raw7944step1Labels = mixedMoment B raw7944step2 raw7944step2Labels := by
      have ha : raw7944step2 = raw7944step1 := by apply Matrix.ext; unfold raw7944step2 raw7944step1; decide +kernel
      have hl : raw7944step1Labels = labelEmbedding1 ∘ raw7944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7944step1 raw7944step1Labels raw7944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw7945 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7945step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7945step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7945step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, -1, 2]]
def raw7945step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7945step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7945step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7945step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7945step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7945 raw7945Labels = mixedMoment B node2787 node2787Labels := by
  calc
    mixedMoment B raw7945 raw7945Labels = mixedMoment B raw7945step0 raw7945step0Labels := by
      have hz : ∀ j, raw7945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7945step0 = (fun i j => raw7945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7945step0 raw7945; decide +kernel
      have hl : raw7945step0Labels = raw7945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7945 raw7945Labels permutation434 hz
    mixedMoment B raw7945step0 raw7945step0Labels = mixedMoment B raw7945step1 raw7945step1Labels := by
      have hz : ∀ j, raw7945step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7945step1 = (fun i j => raw7945step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7945step1 raw7945step0; decide +kernel
      have hl : raw7945step1Labels = raw7945step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7945step0 raw7945step0Labels permutation80 hz
    mixedMoment B raw7945step1 raw7945step1Labels = mixedMoment B raw7945step2 raw7945step2Labels := by
      have hz : ∀ j, raw7945step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7945step2 = (fun i j => raw7945step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7945step2 raw7945step1; decide +kernel
      have hl : raw7945step2Labels = raw7945step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7945step1 raw7945step1Labels permutation14 hz
    mixedMoment B raw7945step2 raw7945step2Labels = mixedMoment B raw7945step3 raw7945step3Labels := by
      have ha : raw7945step3 = (fun i j => raw7945step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7945step3 raw7945step2; decide +kernel
      have hl : raw7945step3Labels = raw7945step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7945step2 raw7945step2Labels permutation2 permutation7
    mixedMoment B raw7945step3 raw7945step3Labels = mixedMoment B raw7945step4 raw7945step4Labels := by
      have ha : raw7945step4 = raw7945step3 := by apply Matrix.ext; unfold raw7945step4 raw7945step3; decide +kernel
      have hl : raw7945step3Labels = labelEmbedding1 ∘ raw7945step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7945step3 raw7945step3Labels raw7945step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2787 node2787Labels := by rfl

def raw7946 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7946step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7946step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7946step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7946step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7946step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7946 raw7946Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw7946 raw7946Labels = mixedMoment B raw7946step0 raw7946step0Labels := by
      have hz : ∀ j, raw7946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7946step0 = (fun i j => raw7946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7946step0 raw7946; decide +kernel
      have hl : raw7946step0Labels = raw7946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7946 raw7946Labels permutation346 hz
    mixedMoment B raw7946step0 raw7946step0Labels = mixedMoment B raw7946step1 raw7946step1Labels := by
      have hz : ∀ j, raw7946step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7946step1 = (fun i j => raw7946step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7946step1 raw7946step0; decide +kernel
      have hl : raw7946step1Labels = raw7946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7946step0 raw7946step0Labels permutation56 hz
    mixedMoment B raw7946step1 raw7946step1Labels = mixedMoment B raw7946step2 raw7946step2Labels := by
      have ha : raw7946step2 = (fun i j => raw7946step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7946step2 raw7946step1; decide +kernel
      have hl : raw7946step2Labels = raw7946step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7946step1 raw7946step1Labels permutation8 permutation7
    mixedMoment B raw7946step2 raw7946step2Labels = mixedMoment B raw7946step3 raw7946step3Labels := by
      have ha : raw7946step3 = raw7946step2 := by apply Matrix.ext; unfold raw7946step3 raw7946step2; decide +kernel
      have hl : raw7946step2Labels = labelEmbedding1 ∘ raw7946step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7946step2 raw7946step2Labels raw7946step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw7947 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7947step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7947step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7947step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7947 raw7947Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw7947 raw7947Labels = mixedMoment B raw7947step0 raw7947step0Labels := by
      have hz : ∀ j, raw7947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7947step0 = (fun i j => raw7947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7947step0 raw7947; decide +kernel
      have hl : raw7947step0Labels = raw7947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7947 raw7947Labels permutation346 hz
    mixedMoment B raw7947step0 raw7947step0Labels = mixedMoment B raw7947step1 raw7947step1Labels := by
      have hz : ∀ j, raw7947step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7947step1 = (fun i j => raw7947step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7947step1 raw7947step0; decide +kernel
      have hl : raw7947step1Labels = raw7947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7947step0 raw7947step0Labels permutation56 hz
    mixedMoment B raw7947step1 raw7947step1Labels = mixedMoment B raw7947step2 raw7947step2Labels := by
      have ha : raw7947step2 = (fun i j => raw7947step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7947step2 raw7947step1; decide +kernel
      have hl : raw7947step2Labels = raw7947step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7947step1 raw7947step1Labels permutation8 permutation7
    mixedMoment B raw7947step2 raw7947step2Labels = mixedMoment B raw7947step3 raw7947step3Labels := by
      have ha : raw7947step3 = raw7947step2 := by apply Matrix.ext; unfold raw7947step3 raw7947step2; decide +kernel
      have hl : raw7947step2Labels = labelEmbedding1 ∘ raw7947step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7947step2 raw7947step2Labels raw7947step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw7948 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7948step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7948 raw7948Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw7948 raw7948Labels = mixedMoment B raw7948step0 raw7948step0Labels := by
      have ha : raw7948step0 = (fun i j => raw7948 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7948step0 raw7948; decide +kernel
      have hl : raw7948step0Labels = raw7948Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7948 raw7948Labels permutation158 permutation7
    mixedMoment B raw7948step0 raw7948step0Labels = mixedMoment B raw7948step1 raw7948step1Labels := by
      have ha : raw7948step1 = raw7948step0 := by apply Matrix.ext; unfold raw7948step1 raw7948step0; decide +kernel
      have hl : raw7948step0Labels = labelEmbedding1 ∘ raw7948step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7948step0 raw7948step0Labels raw7948step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw7949 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7949step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7949step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7949step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7949step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7949step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7949step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7949 raw7949Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw7949 raw7949Labels = mixedMoment B raw7949step0 raw7949step0Labels := by
      have hz : ∀ j, raw7949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7949step0 = (fun i j => raw7949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7949step0 raw7949; decide +kernel
      have hl : raw7949step0Labels = raw7949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7949 raw7949Labels permutation434 hz
    mixedMoment B raw7949step0 raw7949step0Labels = mixedMoment B raw7949step1 raw7949step1Labels := by
      have hz : ∀ j, raw7949step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7949step1 = (fun i j => raw7949step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7949step1 raw7949step0; decide +kernel
      have hl : raw7949step1Labels = raw7949step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7949step0 raw7949step0Labels permutation80 hz
    mixedMoment B raw7949step1 raw7949step1Labels = mixedMoment B raw7949step2 raw7949step2Labels := by
      have ha : raw7949step2 = (fun i j => raw7949step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7949step2 raw7949step1; decide +kernel
      have hl : raw7949step2Labels = raw7949step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7949step1 raw7949step1Labels permutation8 permutation7
    mixedMoment B raw7949step2 raw7949step2Labels = mixedMoment B raw7949step3 raw7949step3Labels := by
      have ha : raw7949step3 = raw7949step2 := by apply Matrix.ext; unfold raw7949step3 raw7949step2; decide +kernel
      have hl : raw7949step2Labels = labelEmbedding1 ∘ raw7949step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7949step2 raw7949step2Labels raw7949step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw7950 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7950step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7950 raw7950Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw7950 raw7950Labels = mixedMoment B raw7950step0 raw7950step0Labels := by
      have hz : ∀ j, raw7950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7950step0 = (fun i j => raw7950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7950step0 raw7950; decide +kernel
      have hl : raw7950step0Labels = raw7950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7950 raw7950Labels permutation346 hz
    mixedMoment B raw7950step0 raw7950step0Labels = mixedMoment B raw7950step1 raw7950step1Labels := by
      have ha : raw7950step1 = (fun i j => raw7950step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7950step1 raw7950step0; decide +kernel
      have hl : raw7950step1Labels = raw7950step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7950step0 raw7950step0Labels permutation32 permutation7
    mixedMoment B raw7950step1 raw7950step1Labels = mixedMoment B raw7950step2 raw7950step2Labels := by
      have ha : raw7950step2 = raw7950step1 := by apply Matrix.ext; unfold raw7950step2 raw7950step1; decide +kernel
      have hl : raw7950step1Labels = labelEmbedding1 ∘ raw7950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7950step1 raw7950step1Labels raw7950step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw7951 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7951step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7951step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7951step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7951step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7951step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7951 raw7951Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw7951 raw7951Labels = mixedMoment B raw7951step0 raw7951step0Labels := by
      have hz : ∀ j, raw7951 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7951step0 = (fun i j => raw7951 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7951step0 raw7951; decide +kernel
      have hl : raw7951step0Labels = raw7951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7951 raw7951Labels permutation346 hz
    mixedMoment B raw7951step0 raw7951step0Labels = mixedMoment B raw7951step1 raw7951step1Labels := by
      have hz : ∀ j, raw7951step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7951step1 = (fun i j => raw7951step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7951step1 raw7951step0; decide +kernel
      have hl : raw7951step1Labels = raw7951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7951step0 raw7951step0Labels permutation56 hz
    mixedMoment B raw7951step1 raw7951step1Labels = mixedMoment B raw7951step2 raw7951step2Labels := by
      have ha : raw7951step2 = (fun i j => raw7951step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7951step2 raw7951step1; decide +kernel
      have hl : raw7951step2Labels = raw7951step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7951step1 raw7951step1Labels permutation8 permutation7
    mixedMoment B raw7951step2 raw7951step2Labels = mixedMoment B raw7951step3 raw7951step3Labels := by
      have ha : raw7951step3 = raw7951step2 := by apply Matrix.ext; unfold raw7951step3 raw7951step2; decide +kernel
      have hl : raw7951step2Labels = labelEmbedding1 ∘ raw7951step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7951step2 raw7951step2Labels raw7951step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw7952 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7952 raw7952Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw7952 raw7952Labels = mixedMoment B raw7952step0 raw7952step0Labels := by
      have hz : ∀ j, raw7952 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7952step0 = (fun i j => raw7952 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7952step0 raw7952; decide +kernel
      have hl : raw7952step0Labels = raw7952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7952 raw7952Labels permutation265 hz
    mixedMoment B raw7952step0 raw7952step0Labels = mixedMoment B raw7952step1 raw7952step1Labels := by
      have ha : raw7952step1 = (fun i j => raw7952step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7952step1 raw7952step0; decide +kernel
      have hl : raw7952step1Labels = raw7952step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7952step0 raw7952step0Labels permutation38 permutation7
    mixedMoment B raw7952step1 raw7952step1Labels = mixedMoment B raw7952step2 raw7952step2Labels := by
      have ha : raw7952step2 = raw7952step1 := by apply Matrix.ext; unfold raw7952step2 raw7952step1; decide +kernel
      have hl : raw7952step1Labels = labelEmbedding1 ∘ raw7952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7952step1 raw7952step1Labels raw7952step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw7953 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7953step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7953step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7953step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7953step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7953step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7953step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7953 raw7953Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw7953 raw7953Labels = mixedMoment B raw7953step0 raw7953step0Labels := by
      have hz : ∀ j, raw7953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7953step0 = (fun i j => raw7953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7953step0 raw7953; decide +kernel
      have hl : raw7953step0Labels = raw7953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7953 raw7953Labels permutation346 hz
    mixedMoment B raw7953step0 raw7953step0Labels = mixedMoment B raw7953step1 raw7953step1Labels := by
      have hz : ∀ j, raw7953step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7953step1 = (fun i j => raw7953step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7953step1 raw7953step0; decide +kernel
      have hl : raw7953step1Labels = raw7953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7953step0 raw7953step0Labels permutation56 hz
    mixedMoment B raw7953step1 raw7953step1Labels = mixedMoment B raw7953step2 raw7953step2Labels := by
      have ha : raw7953step2 = (fun i j => raw7953step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7953step2 raw7953step1; decide +kernel
      have hl : raw7953step2Labels = raw7953step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7953step1 raw7953step1Labels permutation10 permutation5
    mixedMoment B raw7953step2 raw7953step2Labels = mixedMoment B raw7953step3 raw7953step3Labels := by
      have ha : raw7953step3 = -raw7953step2 := by apply Matrix.ext; change ∀ i j, raw7953step3 i j = -(raw7953step2 i j); unfold raw7953step3 raw7953step2; decide +kernel
      have hl : raw7953step3Labels = raw7953step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7953step3 raw7953step3Labels = mixedMoment B raw7953step4 raw7953step4Labels := by
      have ha : raw7953step4 = raw7953step3 := by apply Matrix.ext; unfold raw7953step4 raw7953step3; decide +kernel
      have hl : raw7953step3Labels = labelEmbedding1 ∘ raw7953step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7953step3 raw7953step3Labels raw7953step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw7954 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7954step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7954 raw7954Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw7954 raw7954Labels = mixedMoment B raw7954step0 raw7954step0Labels := by
      have hz : ∀ j, raw7954 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7954step0 = (fun i j => raw7954 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7954step0 raw7954; decide +kernel
      have hl : raw7954step0Labels = raw7954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7954 raw7954Labels permutation265 hz
    mixedMoment B raw7954step0 raw7954step0Labels = mixedMoment B raw7954step1 raw7954step1Labels := by
      have ha : raw7954step1 = (fun i j => raw7954step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7954step1 raw7954step0; decide +kernel
      have hl : raw7954step1Labels = raw7954step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7954step0 raw7954step0Labels permutation38 permutation7
    mixedMoment B raw7954step1 raw7954step1Labels = mixedMoment B raw7954step2 raw7954step2Labels := by
      have ha : raw7954step2 = raw7954step1 := by apply Matrix.ext; unfold raw7954step2 raw7954step1; decide +kernel
      have hl : raw7954step1Labels = labelEmbedding1 ∘ raw7954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7954step1 raw7954step1Labels raw7954step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw7955 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7955step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7955step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![0, -2, 2]]
def raw7955step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7955step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7955step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7955step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7955step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7955 raw7955Labels = mixedMoment B node3124 node3124Labels := by
  calc
    mixedMoment B raw7955 raw7955Labels = mixedMoment B raw7955step0 raw7955step0Labels := by
      have hz : ∀ j, raw7955 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7955step0 = (fun i j => raw7955 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7955step0 raw7955; decide +kernel
      have hl : raw7955step0Labels = raw7955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7955 raw7955Labels permutation434 hz
    mixedMoment B raw7955step0 raw7955step0Labels = mixedMoment B raw7955step1 raw7955step1Labels := by
      have hz : ∀ j, raw7955step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7955step1 = (fun i j => raw7955step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7955step1 raw7955step0; decide +kernel
      have hl : raw7955step1Labels = raw7955step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7955step0 raw7955step0Labels permutation80 hz
    mixedMoment B raw7955step1 raw7955step1Labels = mixedMoment B raw7955step2 raw7955step2Labels := by
      have hz : ∀ j, raw7955step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7955step2 = (fun i j => raw7955step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7955step2 raw7955step1; decide +kernel
      have hl : raw7955step2Labels = raw7955step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7955step1 raw7955step1Labels permutation14 hz
    mixedMoment B raw7955step2 raw7955step2Labels = mixedMoment B raw7955step3 raw7955step3Labels := by
      have ha : raw7955step3 = (fun i j => raw7955step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7955step3 raw7955step2; decide +kernel
      have hl : raw7955step3Labels = raw7955step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7955step2 raw7955step2Labels permutation2 permutation7
    mixedMoment B raw7955step3 raw7955step3Labels = mixedMoment B raw7955step4 raw7955step4Labels := by
      have ha : raw7955step4 = raw7955step3 := by apply Matrix.ext; unfold raw7955step4 raw7955step3; decide +kernel
      have hl : raw7955step3Labels = labelEmbedding1 ∘ raw7955step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7955step3 raw7955step3Labels raw7955step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3124 node3124Labels := by rfl

def raw7956 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7956step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7956step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7956step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7956step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7956 raw7956Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw7956 raw7956Labels = mixedMoment B raw7956step0 raw7956step0Labels := by
      have hz : ∀ j, raw7956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7956step0 = (fun i j => raw7956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7956step0 raw7956; decide +kernel
      have hl : raw7956step0Labels = raw7956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7956 raw7956Labels permutation346 hz
    mixedMoment B raw7956step0 raw7956step0Labels = mixedMoment B raw7956step1 raw7956step1Labels := by
      have hz : ∀ j, raw7956step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7956step1 = (fun i j => raw7956step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7956step1 raw7956step0; decide +kernel
      have hl : raw7956step1Labels = raw7956step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7956step0 raw7956step0Labels permutation56 hz
    mixedMoment B raw7956step1 raw7956step1Labels = mixedMoment B raw7956step2 raw7956step2Labels := by
      have ha : raw7956step2 = (fun i j => raw7956step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7956step2 raw7956step1; decide +kernel
      have hl : raw7956step2Labels = raw7956step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7956step1 raw7956step1Labels permutation8 permutation7
    mixedMoment B raw7956step2 raw7956step2Labels = mixedMoment B raw7956step3 raw7956step3Labels := by
      have ha : raw7956step3 = raw7956step2 := by apply Matrix.ext; unfold raw7956step3 raw7956step2; decide +kernel
      have hl : raw7956step2Labels = labelEmbedding1 ∘ raw7956step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7956step2 raw7956step2Labels raw7956step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw7957 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7957step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7957 raw7957Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw7957 raw7957Labels = mixedMoment B raw7957step0 raw7957step0Labels := by
      have hz : ∀ j, raw7957 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7957step0 = (fun i j => raw7957 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7957step0 raw7957; decide +kernel
      have hl : raw7957step0Labels = raw7957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7957 raw7957Labels permutation265 hz
    mixedMoment B raw7957step0 raw7957step0Labels = mixedMoment B raw7957step1 raw7957step1Labels := by
      have ha : raw7957step1 = (fun i j => raw7957step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7957step1 raw7957step0; decide +kernel
      have hl : raw7957step1Labels = raw7957step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7957step0 raw7957step0Labels permutation38 permutation2
    mixedMoment B raw7957step1 raw7957step1Labels = mixedMoment B raw7957step2 raw7957step2Labels := by
      have ha : raw7957step2 = -raw7957step1 := by apply Matrix.ext; change ∀ i j, raw7957step2 i j = -(raw7957step1 i j); unfold raw7957step2 raw7957step1; decide +kernel
      have hl : raw7957step2Labels = raw7957step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw7958 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7958step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, -1, 2]]
def raw7958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7958step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]
def raw7958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7958 raw7958Labels = mixedMoment B node3635 node3635Labels := by
  calc
    mixedMoment B raw7958 raw7958Labels = mixedMoment B raw7958step0 raw7958step0Labels := by
      have hz : ∀ j, raw7958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7958step0 = (fun i j => raw7958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7958step0 raw7958; decide +kernel
      have hl : raw7958step0Labels = raw7958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7958 raw7958Labels permutation434 hz
    mixedMoment B raw7958step0 raw7958step0Labels = mixedMoment B raw7958step1 raw7958step1Labels := by
      have hz : ∀ j, raw7958step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7958step1 = (fun i j => raw7958step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7958step1 raw7958step0; decide +kernel
      have hl : raw7958step1Labels = raw7958step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7958step0 raw7958step0Labels permutation80 hz
    mixedMoment B raw7958step1 raw7958step1Labels = mixedMoment B raw7958step2 raw7958step2Labels := by
      have hz : ∀ j, raw7958step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7958step2 = (fun i j => raw7958step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7958step2 raw7958step1; decide +kernel
      have hl : raw7958step2Labels = raw7958step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7958step1 raw7958step1Labels permutation14 hz
    mixedMoment B raw7958step2 raw7958step2Labels = mixedMoment B raw7958step3 raw7958step3Labels := by
      have ha : raw7958step3 = -raw7958step2 := by apply Matrix.ext; change ∀ i j, raw7958step3 i j = -(raw7958step2 i j); unfold raw7958step3 raw7958step2; decide +kernel
      have hl : raw7958step3Labels = raw7958step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3635 node3635Labels := by rfl

def raw7959 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw7959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7959step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7959step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7959 raw7959Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw7959 raw7959Labels = mixedMoment B raw7959step0 raw7959step0Labels := by
      have hz : ∀ j, raw7959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7959step0 = (fun i j => raw7959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7959step0 raw7959; decide +kernel
      have hl : raw7959step0Labels = raw7959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7959 raw7959Labels permutation346 hz
    mixedMoment B raw7959step0 raw7959step0Labels = mixedMoment B raw7959step1 raw7959step1Labels := by
      have hz : ∀ j, raw7959step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7959step1 = (fun i j => raw7959step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7959step1 raw7959step0; decide +kernel
      have hl : raw7959step1Labels = raw7959step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7959step0 raw7959step0Labels permutation56 hz
    mixedMoment B raw7959step1 raw7959step1Labels = mixedMoment B raw7959step2 raw7959step2Labels := by
      have ha : raw7959step2 = (fun i j => raw7959step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7959step2 raw7959step1; decide +kernel
      have hl : raw7959step2Labels = raw7959step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7959step1 raw7959step1Labels permutation9 permutation2
    mixedMoment B raw7959step2 raw7959step2Labels = mixedMoment B raw7959step3 raw7959step3Labels := by
      have ha : raw7959step3 = -raw7959step2 := by apply Matrix.ext; change ∀ i j, raw7959step3 i j = -(raw7959step2 i j); unfold raw7959step3 raw7959step2; decide +kernel
      have hl : raw7959step3Labels = raw7959step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw7960 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7960 raw7960Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw7960 raw7960Labels = mixedMoment B raw7960step0 raw7960step0Labels := by
      have hz : ∀ j, raw7960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7960step0 = (fun i j => raw7960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7960step0 raw7960; decide +kernel
      have hl : raw7960step0Labels = raw7960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7960 raw7960Labels permutation346 hz
    mixedMoment B raw7960step0 raw7960step0Labels = mixedMoment B raw7960step1 raw7960step1Labels := by
      have hz : ∀ j, raw7960step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7960step1 = (fun i j => raw7960step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7960step1 raw7960step0; decide +kernel
      have hl : raw7960step1Labels = raw7960step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7960step0 raw7960step0Labels permutation56 hz
    mixedMoment B raw7960step1 raw7960step1Labels = mixedMoment B raw7960step2 raw7960step2Labels := by
      have ha : raw7960step2 = -raw7960step1 := by apply Matrix.ext; change ∀ i j, raw7960step2 i j = -(raw7960step1 i j); unfold raw7960step2 raw7960step1; decide +kernel
      have hl : raw7960step2Labels = raw7960step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw7961 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7961step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7961 raw7961Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw7961 raw7961Labels = mixedMoment B raw7961step0 raw7961step0Labels := by
      have hz : ∀ j, raw7961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7961step0 = (fun i j => raw7961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7961step0 raw7961; decide +kernel
      have hl : raw7961step0Labels = raw7961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7961 raw7961Labels permutation346 hz
    mixedMoment B raw7961step0 raw7961step0Labels = mixedMoment B raw7961step1 raw7961step1Labels := by
      have hz : ∀ j, raw7961step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7961step1 = (fun i j => raw7961step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7961step1 raw7961step0; decide +kernel
      have hl : raw7961step1Labels = raw7961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7961step0 raw7961step0Labels permutation56 hz
    mixedMoment B raw7961step1 raw7961step1Labels = mixedMoment B raw7961step2 raw7961step2Labels := by
      have ha : raw7961step2 = (fun i j => raw7961step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7961step2 raw7961step1; decide +kernel
      have hl : raw7961step2Labels = raw7961step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7961step1 raw7961step1Labels permutation8 permutation4
    mixedMoment B raw7961step2 raw7961step2Labels = mixedMoment B raw7961step3 raw7961step3Labels := by
      have ha : raw7961step3 = -raw7961step2 := by apply Matrix.ext; change ∀ i j, raw7961step3 i j = -(raw7961step2 i j); unfold raw7961step3 raw7961step2; decide +kernel
      have hl : raw7961step3Labels = raw7961step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw7962 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7962step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7962 raw7962Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw7962 raw7962Labels = mixedMoment B raw7962step0 raw7962step0Labels := by
      have hz : ∀ j, raw7962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7962step0 = (fun i j => raw7962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7962step0 raw7962; decide +kernel
      have hl : raw7962step0Labels = raw7962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7962 raw7962Labels permutation346 hz
    mixedMoment B raw7962step0 raw7962step0Labels = mixedMoment B raw7962step1 raw7962step1Labels := by
      have hz : ∀ j, raw7962step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7962step1 = (fun i j => raw7962step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7962step1 raw7962step0; decide +kernel
      have hl : raw7962step1Labels = raw7962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7962step0 raw7962step0Labels permutation56 hz
    mixedMoment B raw7962step1 raw7962step1Labels = mixedMoment B raw7962step2 raw7962step2Labels := by
      have ha : raw7962step2 = (fun i j => raw7962step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7962step2 raw7962step1; decide +kernel
      have hl : raw7962step2Labels = raw7962step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7962step1 raw7962step1Labels permutation10 permutation4
    mixedMoment B raw7962step2 raw7962step2Labels = mixedMoment B raw7962step3 raw7962step3Labels := by
      have ha : raw7962step3 = -raw7962step2 := by apply Matrix.ext; change ∀ i j, raw7962step3 i j = -(raw7962step2 i j); unfold raw7962step3 raw7962step2; decide +kernel
      have hl : raw7962step3Labels = raw7962step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw7963 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw7963step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7963 raw7963Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw7963 raw7963Labels = mixedMoment B raw7963step0 raw7963step0Labels := by
      have hz : ∀ j, raw7963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7963step0 = (fun i j => raw7963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7963step0 raw7963; decide +kernel
      have hl : raw7963step0Labels = raw7963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7963 raw7963Labels permutation434 hz
    mixedMoment B raw7963step0 raw7963step0Labels = mixedMoment B raw7963step1 raw7963step1Labels := by
      have hz : ∀ j, raw7963step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7963step1 = (fun i j => raw7963step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7963step1 raw7963step0; decide +kernel
      have hl : raw7963step1Labels = raw7963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7963step0 raw7963step0Labels permutation80 hz
    mixedMoment B raw7963step1 raw7963step1Labels = mixedMoment B raw7963step2 raw7963step2Labels := by
      have ha : raw7963step2 = (fun i j => raw7963step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7963step2 raw7963step1; decide +kernel
      have hl : raw7963step2Labels = raw7963step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7963step1 raw7963step1Labels permutation10 permutation4
    mixedMoment B raw7963step2 raw7963step2Labels = mixedMoment B raw7963step3 raw7963step3Labels := by
      have ha : raw7963step3 = -raw7963step2 := by apply Matrix.ext; change ∀ i j, raw7963step3 i j = -(raw7963step2 i j); unfold raw7963step3 raw7963step2; decide +kernel
      have hl : raw7963step3Labels = raw7963step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3627 node3627Labels := by rfl

def raw7964 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7964step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![0, -2, 2]]
def raw7964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7964step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-2, 0, 2]]
def raw7964step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7964step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]
def raw7964step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7964 raw7964Labels = mixedMoment B node3629 node3629Labels := by
  calc
    mixedMoment B raw7964 raw7964Labels = mixedMoment B raw7964step0 raw7964step0Labels := by
      have hz : ∀ j, raw7964 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7964step0 = (fun i j => raw7964 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7964step0 raw7964; decide +kernel
      have hl : raw7964step0Labels = raw7964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7964 raw7964Labels permutation434 hz
    mixedMoment B raw7964step0 raw7964step0Labels = mixedMoment B raw7964step1 raw7964step1Labels := by
      have hz : ∀ j, raw7964step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7964step1 = (fun i j => raw7964step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7964step1 raw7964step0; decide +kernel
      have hl : raw7964step1Labels = raw7964step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7964step0 raw7964step0Labels permutation80 hz
    mixedMoment B raw7964step1 raw7964step1Labels = mixedMoment B raw7964step2 raw7964step2Labels := by
      have hz : ∀ j, raw7964step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7964step2 = (fun i j => raw7964step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7964step2 raw7964step1; decide +kernel
      have hl : raw7964step2Labels = raw7964step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7964step1 raw7964step1Labels permutation14 hz
    mixedMoment B raw7964step2 raw7964step2Labels = mixedMoment B raw7964step3 raw7964step3Labels := by
      have ha : raw7964step3 = (fun i j => raw7964step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7964step3 raw7964step2; decide +kernel
      have hl : raw7964step3Labels = raw7964step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7964step2 raw7964step2Labels permutation2 permutation4
    mixedMoment B raw7964step3 raw7964step3Labels = mixedMoment B raw7964step4 raw7964step4Labels := by
      have ha : raw7964step4 = -raw7964step3 := by apply Matrix.ext; change ∀ i j, raw7964step4 i j = -(raw7964step3 i j); unfold raw7964step4 raw7964step3; decide +kernel
      have hl : raw7964step4Labels = raw7964step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3629 node3629Labels := by rfl

def raw7965 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7965 raw7965Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw7965 raw7965Labels = mixedMoment B raw7965step0 raw7965step0Labels := by
      have hz : ∀ j, raw7965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7965step0 = (fun i j => raw7965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7965step0 raw7965; decide +kernel
      have hl : raw7965step0Labels = raw7965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7965 raw7965Labels permutation346 hz
    mixedMoment B raw7965step0 raw7965step0Labels = mixedMoment B raw7965step1 raw7965step1Labels := by
      have ha : raw7965step1 = (fun i j => raw7965step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7965step1 raw7965step0; decide +kernel
      have hl : raw7965step1Labels = raw7965step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7965step0 raw7965step0Labels permutation44 permutation4
    mixedMoment B raw7965step1 raw7965step1Labels = mixedMoment B raw7965step2 raw7965step2Labels := by
      have ha : raw7965step2 = -raw7965step1 := by apply Matrix.ext; change ∀ i j, raw7965step2 i j = -(raw7965step1 i j); unfold raw7965step2 raw7965step1; decide +kernel
      have hl : raw7965step2Labels = raw7965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw7966 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7966step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7966 raw7966Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw7966 raw7966Labels = mixedMoment B raw7966step0 raw7966step0Labels := by
      have hz : ∀ j, raw7966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7966step0 = (fun i j => raw7966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7966step0 raw7966; decide +kernel
      have hl : raw7966step0Labels = raw7966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7966 raw7966Labels permutation346 hz
    mixedMoment B raw7966step0 raw7966step0Labels = mixedMoment B raw7966step1 raw7966step1Labels := by
      have hz : ∀ j, raw7966step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7966step1 = (fun i j => raw7966step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7966step1 raw7966step0; decide +kernel
      have hl : raw7966step1Labels = raw7966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7966step0 raw7966step0Labels permutation56 hz
    mixedMoment B raw7966step1 raw7966step1Labels = mixedMoment B raw7966step2 raw7966step2Labels := by
      have ha : raw7966step2 = (fun i j => raw7966step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7966step2 raw7966step1; decide +kernel
      have hl : raw7966step2Labels = raw7966step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7966step1 raw7966step1Labels permutation10 permutation4
    mixedMoment B raw7966step2 raw7966step2Labels = mixedMoment B raw7966step3 raw7966step3Labels := by
      have ha : raw7966step3 = -raw7966step2 := by apply Matrix.ext; change ∀ i j, raw7966step3 i j = -(raw7966step2 i j); unfold raw7966step3 raw7966step2; decide +kernel
      have hl : raw7966step3Labels = raw7966step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw7967 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7967 raw7967Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw7967 raw7967Labels = mixedMoment B raw7967step0 raw7967step0Labels := by
      have hz : ∀ j, raw7967 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7967step0 = (fun i j => raw7967 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7967step0 raw7967; decide +kernel
      have hl : raw7967step0Labels = raw7967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7967 raw7967Labels permutation265 hz
    mixedMoment B raw7967step0 raw7967step0Labels = mixedMoment B raw7967step1 raw7967step1Labels := by
      have ha : raw7967step1 = (fun i j => raw7967step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7967step1 raw7967step0; decide +kernel
      have hl : raw7967step1Labels = raw7967step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7967step0 raw7967step0Labels permutation34 permutation4
    mixedMoment B raw7967step1 raw7967step1Labels = mixedMoment B raw7967step2 raw7967step2Labels := by
      have ha : raw7967step2 = -raw7967step1 := by apply Matrix.ext; change ∀ i j, raw7967step2 i j = -(raw7967step1 i j); unfold raw7967step2 raw7967step1; decide +kernel
      have hl : raw7967step2Labels = raw7967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw7968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7968step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7968step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7968 raw7968Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw7968 raw7968Labels = mixedMoment B raw7968step0 raw7968step0Labels := by
      have hz : ∀ j, raw7968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7968step0 = (fun i j => raw7968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7968step0 raw7968; decide +kernel
      have hl : raw7968step0Labels = raw7968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7968 raw7968Labels permutation346 hz
    mixedMoment B raw7968step0 raw7968step0Labels = mixedMoment B raw7968step1 raw7968step1Labels := by
      have ha : raw7968step1 = (fun i j => raw7968step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7968step1 raw7968step0; decide +kernel
      have hl : raw7968step1Labels = raw7968step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7968step0 raw7968step0Labels permutation40 permutation3
    mixedMoment B raw7968step1 raw7968step1Labels = mixedMoment B raw7968step2 raw7968step2Labels := by
      have ha : raw7968step2 = raw7968step1 := by apply Matrix.ext; unfold raw7968step2 raw7968step1; decide +kernel
      have hl : raw7968step1Labels = labelEmbedding6 ∘ raw7968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7968step1 raw7968step1Labels raw7968step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw7969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7969 raw7969Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw7969 raw7969Labels = mixedMoment B raw7969step0 raw7969step0Labels := by
      have ha : raw7969step0 = (fun i j => raw7969 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7969step0 raw7969; decide +kernel
      have hl : raw7969step0Labels = raw7969Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7969 raw7969Labels permutation182 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw7970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7970step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7970 raw7970Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw7970 raw7970Labels = mixedMoment B raw7970step0 raw7970step0Labels := by
      have hz : ∀ j, raw7970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7970step0 = (fun i j => raw7970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7970step0 raw7970; decide +kernel
      have hl : raw7970step0Labels = raw7970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7970 raw7970Labels permutation346 hz
    mixedMoment B raw7970step0 raw7970step0Labels = mixedMoment B raw7970step1 raw7970step1Labels := by
      have ha : raw7970step1 = (fun i j => raw7970step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7970step1 raw7970step0; decide +kernel
      have hl : raw7970step1Labels = raw7970step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7970step0 raw7970step0Labels permutation38 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw7971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7971 raw7971Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw7971 raw7971Labels = mixedMoment B raw7971step0 raw7971step0Labels := by
      have hz : ∀ j, raw7971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7971step0 = (fun i j => raw7971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7971step0 raw7971; decide +kernel
      have hl : raw7971step0Labels = raw7971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7971 raw7971Labels permutation346 hz
    mixedMoment B raw7971step0 raw7971step0Labels = mixedMoment B raw7971step1 raw7971step1Labels := by
      have ha : raw7971step1 = (fun i j => raw7971step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7971step1 raw7971step0; decide +kernel
      have hl : raw7971step1Labels = raw7971step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7971step0 raw7971step0Labels permutation39 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw7972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7972step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7972step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7972 raw7972Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw7972 raw7972Labels = mixedMoment B raw7972step0 raw7972step0Labels := by
      have hz : ∀ j, raw7972 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7972step0 = (fun i j => raw7972 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7972step0 raw7972; decide +kernel
      have hl : raw7972step0Labels = raw7972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7972 raw7972Labels permutation265 hz
    mixedMoment B raw7972step0 raw7972step0Labels = mixedMoment B raw7972step1 raw7972step1Labels := by
      have ha : raw7972step1 = (fun i j => raw7972step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7972step1 raw7972step0; decide +kernel
      have hl : raw7972step1Labels = raw7972step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7972step0 raw7972step0Labels permutation40 permutation3
    mixedMoment B raw7972step1 raw7972step1Labels = mixedMoment B raw7972step2 raw7972step2Labels := by
      have ha : raw7972step2 = raw7972step1 := by apply Matrix.ext; unfold raw7972step2 raw7972step1; decide +kernel
      have hl : raw7972step1Labels = labelEmbedding6 ∘ raw7972step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7972step1 raw7972step1Labels raw7972step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw7973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7973 raw7973Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw7973 raw7973Labels = mixedMoment B raw7973step0 raw7973step0Labels := by
      have ha : raw7973step0 = (fun i j => raw7973 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7973step0 raw7973; decide +kernel
      have hl : raw7973step0Labels = raw7973Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7973 raw7973Labels permutation158 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw7974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7974 raw7974Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw7974 raw7974Labels = mixedMoment B raw7974step0 raw7974step0Labels := by
      have hz : ∀ j, raw7974 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7974step0 = (fun i j => raw7974 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7974step0 raw7974; decide +kernel
      have hl : raw7974step0Labels = raw7974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7974 raw7974Labels permutation265 hz
    mixedMoment B raw7974step0 raw7974step0Labels = mixedMoment B raw7974step1 raw7974step1Labels := by
      have ha : raw7974step1 = (fun i j => raw7974step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7974step1 raw7974step0; decide +kernel
      have hl : raw7974step1Labels = raw7974step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7974step0 raw7974step0Labels permutation38 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw7975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7975 raw7975Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw7975 raw7975Labels = mixedMoment B raw7975step0 raw7975step0Labels := by
      have hz : ∀ j, raw7975 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7975step0 = (fun i j => raw7975 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7975step0 raw7975; decide +kernel
      have hl : raw7975step0Labels = raw7975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7975 raw7975Labels permutation265 hz
    mixedMoment B raw7975step0 raw7975step0Labels = mixedMoment B raw7975step1 raw7975step1Labels := by
      have ha : raw7975step1 = (fun i j => raw7975step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7975step1 raw7975step0; decide +kernel
      have hl : raw7975step1Labels = raw7975step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7975step0 raw7975step0Labels permutation39 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw7976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7976step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7976step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7976 raw7976Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw7976 raw7976Labels = mixedMoment B raw7976step0 raw7976step0Labels := by
      have hz : ∀ j, raw7976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7976step0 = (fun i j => raw7976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7976step0 raw7976; decide +kernel
      have hl : raw7976step0Labels = raw7976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7976 raw7976Labels permutation346 hz
    mixedMoment B raw7976step0 raw7976step0Labels = mixedMoment B raw7976step1 raw7976step1Labels := by
      have hz : ∀ j, raw7976step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7976step1 = (fun i j => raw7976step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7976step1 raw7976step0; decide +kernel
      have hl : raw7976step1Labels = raw7976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7976step0 raw7976step0Labels permutation56 hz
    mixedMoment B raw7976step1 raw7976step1Labels = mixedMoment B raw7976step2 raw7976step2Labels := by
      have ha : raw7976step2 = (fun i j => raw7976step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7976step2 raw7976step1; decide +kernel
      have hl : raw7976step2Labels = raw7976step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7976step1 raw7976step1Labels permutation8 permutation3
    mixedMoment B raw7976step2 raw7976step2Labels = mixedMoment B raw7976step3 raw7976step3Labels := by
      have ha : raw7976step3 = raw7976step2 := by apply Matrix.ext; unfold raw7976step3 raw7976step2; decide +kernel
      have hl : raw7976step2Labels = labelEmbedding6 ∘ raw7976step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7976step2 raw7976step2Labels raw7976step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw7977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7977 raw7977Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw7977 raw7977Labels = mixedMoment B raw7977step0 raw7977step0Labels := by
      have hz : ∀ j, raw7977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7977step0 = (fun i j => raw7977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7977step0 raw7977; decide +kernel
      have hl : raw7977step0Labels = raw7977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7977 raw7977Labels permutation346 hz
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw7978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7978 raw7978Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw7978 raw7978Labels = mixedMoment B raw7978step0 raw7978step0Labels := by
      have hz : ∀ j, raw7978 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7978step0 = (fun i j => raw7978 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7978step0 raw7978; decide +kernel
      have hl : raw7978step0Labels = raw7978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7978 raw7978Labels permutation265 hz
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw7979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7979step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7979 raw7979Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw7979 raw7979Labels = mixedMoment B raw7979step0 raw7979step0Labels := by
      have hz : ∀ j, raw7979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7979step0 = (fun i j => raw7979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7979step0 raw7979; decide +kernel
      have hl : raw7979step0Labels = raw7979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7979 raw7979Labels permutation346 hz
    mixedMoment B raw7979step0 raw7979step0Labels = mixedMoment B raw7979step1 raw7979step1Labels := by
      have hz : ∀ j, raw7979step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7979step1 = (fun i j => raw7979step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7979step1 raw7979step0; decide +kernel
      have hl : raw7979step1Labels = raw7979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7979step0 raw7979step0Labels permutation56 hz
    mixedMoment B raw7979step1 raw7979step1Labels = mixedMoment B raw7979step2 raw7979step2Labels := by
      have ha : raw7979step2 = (fun i j => raw7979step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7979step2 raw7979step1; decide +kernel
      have hl : raw7979step2Labels = raw7979step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7979step1 raw7979step1Labels permutation12 permutation2
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw7980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7980step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7980step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7980step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7980 raw7980Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw7980 raw7980Labels = mixedMoment B raw7980step0 raw7980step0Labels := by
      have hz : ∀ j, raw7980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7980step0 = (fun i j => raw7980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7980step0 raw7980; decide +kernel
      have hl : raw7980step0Labels = raw7980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7980 raw7980Labels permutation346 hz
    mixedMoment B raw7980step0 raw7980step0Labels = mixedMoment B raw7980step1 raw7980step1Labels := by
      have hz : ∀ j, raw7980step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7980step1 = (fun i j => raw7980step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7980step1 raw7980step0; decide +kernel
      have hl : raw7980step1Labels = raw7980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7980step0 raw7980step0Labels permutation56 hz
    mixedMoment B raw7980step1 raw7980step1Labels = mixedMoment B raw7980step2 raw7980step2Labels := by
      have ha : raw7980step2 = (fun i j => raw7980step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7980step2 raw7980step1; decide +kernel
      have hl : raw7980step2Labels = raw7980step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7980step1 raw7980step1Labels permutation8 permutation3
    mixedMoment B raw7980step2 raw7980step2Labels = mixedMoment B raw7980step3 raw7980step3Labels := by
      have ha : raw7980step3 = raw7980step2 := by apply Matrix.ext; unfold raw7980step3 raw7980step2; decide +kernel
      have hl : raw7980step2Labels = labelEmbedding6 ∘ raw7980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7980step2 raw7980step2Labels raw7980step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw7981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7981 raw7981Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw7981 raw7981Labels = mixedMoment B raw7981step0 raw7981step0Labels := by
      have hz : ∀ j, raw7981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7981step0 = (fun i j => raw7981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7981step0 raw7981; decide +kernel
      have hl : raw7981step0Labels = raw7981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7981 raw7981Labels permutation346 hz
    mixedMoment B raw7981step0 raw7981step0Labels = mixedMoment B raw7981step1 raw7981step1Labels := by
      have ha : raw7981step1 = (fun i j => raw7981step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7981step1 raw7981step0; decide +kernel
      have hl : raw7981step1Labels = raw7981step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7981step0 raw7981step0Labels permutation33 permutation2
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw7982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7982 raw7982Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw7982 raw7982Labels = mixedMoment B raw7982step0 raw7982step0Labels := by
      have hz : ∀ j, raw7982 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7982step0 = (fun i j => raw7982 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7982step0 raw7982; decide +kernel
      have hl : raw7982step0Labels = raw7982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7982 raw7982Labels permutation265 hz
    mixedMoment B raw7982step0 raw7982step0Labels = mixedMoment B raw7982step1 raw7982step1Labels := by
      have ha : raw7982step1 = (fun i j => raw7982step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7982step1 raw7982step0; decide +kernel
      have hl : raw7982step1Labels = raw7982step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7982step0 raw7982step0Labels permutation33 permutation2
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw7983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7983step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7983 raw7983Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw7983 raw7983Labels = mixedMoment B raw7983step0 raw7983step0Labels := by
      have hz : ∀ j, raw7983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7983step0 = (fun i j => raw7983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7983step0 raw7983; decide +kernel
      have hl : raw7983step0Labels = raw7983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7983 raw7983Labels permutation346 hz
    mixedMoment B raw7983step0 raw7983step0Labels = mixedMoment B raw7983step1 raw7983step1Labels := by
      have hz : ∀ j, raw7983step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7983step1 = (fun i j => raw7983step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7983step1 raw7983step0; decide +kernel
      have hl : raw7983step1Labels = raw7983step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7983step0 raw7983step0Labels permutation56 hz
    mixedMoment B raw7983step1 raw7983step1Labels = mixedMoment B raw7983step2 raw7983step2Labels := by
      have ha : raw7983step2 = (fun i j => raw7983step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7983step2 raw7983step1; decide +kernel
      have hl : raw7983step2Labels = raw7983step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7983step1 raw7983step1Labels permutation9 permutation2
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw7984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw7984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw7984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7984step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw7984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7984step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7984 raw7984Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw7984 raw7984Labels = mixedMoment B raw7984step0 raw7984step0Labels := by
      have hz : ∀ j, raw7984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7984step0 = (fun i j => raw7984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7984step0 raw7984; decide +kernel
      have hl : raw7984step0Labels = raw7984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7984 raw7984Labels permutation346 hz
    mixedMoment B raw7984step0 raw7984step0Labels = mixedMoment B raw7984step1 raw7984step1Labels := by
      have hz : ∀ j, raw7984step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7984step1 = (fun i j => raw7984step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7984step1 raw7984step0; decide +kernel
      have hl : raw7984step1Labels = raw7984step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7984step0 raw7984step0Labels permutation56 hz
    mixedMoment B raw7984step1 raw7984step1Labels = mixedMoment B raw7984step2 raw7984step2Labels := by
      have ha : raw7984step2 = (fun i j => raw7984step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7984step2 raw7984step1; decide +kernel
      have hl : raw7984step2Labels = raw7984step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7984step1 raw7984step1Labels permutation9 permutation2
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw7985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7985step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7985 raw7985Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw7985 raw7985Labels = mixedMoment B raw7985step0 raw7985step0Labels := by
      have hz : ∀ j, raw7985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7985step0 = (fun i j => raw7985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7985step0 raw7985; decide +kernel
      have hl : raw7985step0Labels = raw7985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7985 raw7985Labels permutation346 hz
    mixedMoment B raw7985step0 raw7985step0Labels = mixedMoment B raw7985step1 raw7985step1Labels := by
      have ha : raw7985step1 = (fun i j => raw7985step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7985step1 raw7985step0; decide +kernel
      have hl : raw7985step1Labels = raw7985step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7985step0 raw7985step0Labels permutation40 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw7986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7986 raw7986Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw7986 raw7986Labels = mixedMoment B raw7986step0 raw7986step0Labels := by
      have ha : raw7986step0 = (fun i j => raw7986 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7986step0 raw7986; decide +kernel
      have hl : raw7986step0Labels = raw7986Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7986 raw7986Labels permutation184 permutation3
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw7987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7987Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7987step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7987 raw7987Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw7987 raw7987Labels = mixedMoment B raw7987step0 raw7987step0Labels := by
      have hz : ∀ j, raw7987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7987step0 = (fun i j => raw7987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7987step0 raw7987; decide +kernel
      have hl : raw7987step0Labels = raw7987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7987 raw7987Labels permutation346 hz
    mixedMoment B raw7987step0 raw7987step0Labels = mixedMoment B raw7987step1 raw7987step1Labels := by
      have ha : raw7987step1 = (fun i j => raw7987step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7987step1 raw7987step0; decide +kernel
      have hl : raw7987step1Labels = raw7987step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7987step0 raw7987step0Labels permutation40 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw7988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7988Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7988step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7988 raw7988Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw7988 raw7988Labels = mixedMoment B raw7988step0 raw7988step0Labels := by
      have hz : ∀ j, raw7988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7988step0 = (fun i j => raw7988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7988step0 raw7988; decide +kernel
      have hl : raw7988step0Labels = raw7988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7988 raw7988Labels permutation346 hz
    mixedMoment B raw7988step0 raw7988step0Labels = mixedMoment B raw7988step1 raw7988step1Labels := by
      have ha : raw7988step1 = (fun i j => raw7988step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7988step1 raw7988step0; decide +kernel
      have hl : raw7988step1Labels = raw7988step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7988step0 raw7988step0Labels permutation40 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw7989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7989Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7989step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7989 raw7989Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw7989 raw7989Labels = mixedMoment B raw7989step0 raw7989step0Labels := by
      have hz : ∀ j, raw7989 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7989step0 = (fun i j => raw7989 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7989step0 raw7989; decide +kernel
      have hl : raw7989step0Labels = raw7989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7989 raw7989Labels permutation265 hz
    mixedMoment B raw7989step0 raw7989step0Labels = mixedMoment B raw7989step1 raw7989step1Labels := by
      have ha : raw7989step1 = (fun i j => raw7989step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7989step1 raw7989step0; decide +kernel
      have hl : raw7989step1Labels = raw7989step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7989step0 raw7989step0Labels permutation40 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw7990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7990Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7990 raw7990Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw7990 raw7990Labels = mixedMoment B raw7990step0 raw7990step0Labels := by
      have ha : raw7990step0 = (fun i j => raw7990 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7990step0 raw7990; decide +kernel
      have hl : raw7990step0Labels = raw7990Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7990 raw7990Labels permutation160 permutation3
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw7991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7991Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7991step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7991 raw7991Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw7991 raw7991Labels = mixedMoment B raw7991step0 raw7991step0Labels := by
      have hz : ∀ j, raw7991 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7991step0 = (fun i j => raw7991 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7991step0 raw7991; decide +kernel
      have hl : raw7991step0Labels = raw7991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7991 raw7991Labels permutation265 hz
    mixedMoment B raw7991step0 raw7991step0Labels = mixedMoment B raw7991step1 raw7991step1Labels := by
      have ha : raw7991step1 = (fun i j => raw7991step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7991step1 raw7991step0; decide +kernel
      have hl : raw7991step1Labels = raw7991step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7991step0 raw7991step0Labels permutation40 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw7992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7992step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7992 raw7992Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw7992 raw7992Labels = mixedMoment B raw7992step0 raw7992step0Labels := by
      have hz : ∀ j, raw7992 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7992step0 = (fun i j => raw7992 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7992step0 raw7992; decide +kernel
      have hl : raw7992step0Labels = raw7992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7992 raw7992Labels permutation265 hz
    mixedMoment B raw7992step0 raw7992step0Labels = mixedMoment B raw7992step1 raw7992step1Labels := by
      have ha : raw7992step1 = (fun i j => raw7992step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7992step1 raw7992step0; decide +kernel
      have hl : raw7992step1Labels = raw7992step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7992step0 raw7992step0Labels permutation40 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw7993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7993step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7993 raw7993Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw7993 raw7993Labels = mixedMoment B raw7993step0 raw7993step0Labels := by
      have hz : ∀ j, raw7993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7993step0 = (fun i j => raw7993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7993step0 raw7993; decide +kernel
      have hl : raw7993step0Labels = raw7993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7993 raw7993Labels permutation346 hz
    mixedMoment B raw7993step0 raw7993step0Labels = mixedMoment B raw7993step1 raw7993step1Labels := by
      have hz : ∀ j, raw7993step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7993step1 = (fun i j => raw7993step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7993step1 raw7993step0; decide +kernel
      have hl : raw7993step1Labels = raw7993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7993step0 raw7993step0Labels permutation56 hz
    mixedMoment B raw7993step1 raw7993step1Labels = mixedMoment B raw7993step2 raw7993step2Labels := by
      have ha : raw7993step2 = (fun i j => raw7993step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7993step2 raw7993step1; decide +kernel
      have hl : raw7993step2Labels = raw7993step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7993step1 raw7993step1Labels permutation8 permutation3
    _ = mixedMoment B node1300 node1300Labels := by rfl

def raw7994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7994 raw7994Labels = mixedMoment B node2959 node2959Labels := by
  calc
    mixedMoment B raw7994 raw7994Labels = mixedMoment B raw7994step0 raw7994step0Labels := by
      have hz : ∀ j, raw7994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7994step0 = (fun i j => raw7994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7994step0 raw7994; decide +kernel
      have hl : raw7994step0Labels = raw7994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7994 raw7994Labels permutation346 hz
    mixedMoment B raw7994step0 raw7994step0Labels = mixedMoment B raw7994step1 raw7994step1Labels := by
      have ha : raw7994step1 = (fun i j => raw7994step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7994step1 raw7994step0; decide +kernel
      have hl : raw7994step1Labels = raw7994step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7994step0 raw7994step0Labels permutation32 permutation3
    _ = mixedMoment B node2959 node2959Labels := by rfl

def raw7995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7995step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7995 raw7995Labels = mixedMoment B node2959 node2959Labels := by
  calc
    mixedMoment B raw7995 raw7995Labels = mixedMoment B raw7995step0 raw7995step0Labels := by
      have hz : ∀ j, raw7995 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7995step0 = (fun i j => raw7995 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7995step0 raw7995; decide +kernel
      have hl : raw7995step0Labels = raw7995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7995 raw7995Labels permutation265 hz
    mixedMoment B raw7995step0 raw7995step0Labels = mixedMoment B raw7995step1 raw7995step1Labels := by
      have ha : raw7995step1 = (fun i j => raw7995step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7995step1 raw7995step0; decide +kernel
      have hl : raw7995step1Labels = raw7995step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7995step0 raw7995step0Labels permutation32 permutation3
    _ = mixedMoment B node2959 node2959Labels := by rfl

def raw7996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7996step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7996step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7996 raw7996Labels = mixedMoment B node3122 node3122Labels := by
  calc
    mixedMoment B raw7996 raw7996Labels = mixedMoment B raw7996step0 raw7996step0Labels := by
      have hz : ∀ j, raw7996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7996step0 = (fun i j => raw7996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7996step0 raw7996; decide +kernel
      have hl : raw7996step0Labels = raw7996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7996 raw7996Labels permutation346 hz
    mixedMoment B raw7996step0 raw7996step0Labels = mixedMoment B raw7996step1 raw7996step1Labels := by
      have hz : ∀ j, raw7996step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7996step1 = (fun i j => raw7996step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7996step1 raw7996step0; decide +kernel
      have hl : raw7996step1Labels = raw7996step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7996step0 raw7996step0Labels permutation56 hz
    mixedMoment B raw7996step1 raw7996step1Labels = mixedMoment B raw7996step2 raw7996step2Labels := by
      have ha : raw7996step2 = (fun i j => raw7996step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7996step2 raw7996step1; decide +kernel
      have hl : raw7996step2Labels = raw7996step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7996step1 raw7996step1Labels permutation8 permutation3
    _ = mixedMoment B node3122 node3122Labels := by rfl

def raw7997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7997step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7997step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7997 raw7997Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw7997 raw7997Labels = mixedMoment B raw7997step0 raw7997step0Labels := by
      have hz : ∀ j, raw7997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7997step0 = (fun i j => raw7997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7997step0 raw7997; decide +kernel
      have hl : raw7997step0Labels = raw7997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7997 raw7997Labels permutation346 hz
    mixedMoment B raw7997step0 raw7997step0Labels = mixedMoment B raw7997step1 raw7997step1Labels := by
      have hz : ∀ j, raw7997step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7997step1 = (fun i j => raw7997step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7997step1 raw7997step0; decide +kernel
      have hl : raw7997step1Labels = raw7997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7997step0 raw7997step0Labels permutation56 hz
    mixedMoment B raw7997step1 raw7997step1Labels = mixedMoment B raw7997step2 raw7997step2Labels := by
      have ha : raw7997step2 = (fun i j => raw7997step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7997step2 raw7997step1; decide +kernel
      have hl : raw7997step2Labels = raw7997step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7997step1 raw7997step1Labels permutation8 permutation3
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw7998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7998step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7998 raw7998Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw7998 raw7998Labels = mixedMoment B raw7998step0 raw7998step0Labels := by
      have hz : ∀ j, raw7998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7998step0 = (fun i j => raw7998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7998step0 raw7998; decide +kernel
      have hl : raw7998step0Labels = raw7998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7998 raw7998Labels permutation346 hz
    mixedMoment B raw7998step0 raw7998step0Labels = mixedMoment B raw7998step1 raw7998step1Labels := by
      have ha : raw7998step1 = (fun i j => raw7998step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7998step1 raw7998step0; decide +kernel
      have hl : raw7998step1Labels = raw7998step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7998step0 raw7998step0Labels permutation32 permutation3
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw7999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7999step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7999 raw7999Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw7999 raw7999Labels = mixedMoment B raw7999step0 raw7999step0Labels := by
      have hz : ∀ j, raw7999 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7999step0 = (fun i j => raw7999 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7999step0 raw7999; decide +kernel
      have hl : raw7999step0Labels = raw7999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7999 raw7999Labels permutation265 hz
    mixedMoment B raw7999step0 raw7999step0Labels = mixedMoment B raw7999step1 raw7999step1Labels := by
      have ha : raw7999step1 = (fun i j => raw7999step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7999step1 raw7999step0; decide +kernel
      have hl : raw7999step1Labels = raw7999step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7999step0 raw7999step0Labels permutation32 permutation3
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw8000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw8000Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw8000step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw8000step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8000step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8000 raw8000Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw8000 raw8000Labels = mixedMoment B raw8000step0 raw8000step0Labels := by
      have hz : ∀ j, raw8000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8000step0 = (fun i j => raw8000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8000step0 raw8000; decide +kernel
      have hl : raw8000step0Labels = raw8000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8000 raw8000Labels permutation346 hz
    mixedMoment B raw8000step0 raw8000step0Labels = mixedMoment B raw8000step1 raw8000step1Labels := by
      have hz : ∀ j, raw8000step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8000step1 = (fun i j => raw8000step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8000step1 raw8000step0; decide +kernel
      have hl : raw8000step1Labels = raw8000step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8000step0 raw8000step0Labels permutation56 hz
    mixedMoment B raw8000step1 raw8000step1Labels = mixedMoment B raw8000step2 raw8000step2Labels := by
      have ha : raw8000step2 = (fun i j => raw8000step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8000step2 raw8000step1; decide +kernel
      have hl : raw8000step2Labels = raw8000step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8000step1 raw8000step1Labels permutation8 permutation3
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw8001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw8001Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw8001step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw8001step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8001 raw8001Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw8001 raw8001Labels = mixedMoment B raw8001step0 raw8001step0Labels := by
      have hz : ∀ j, raw8001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8001step0 = (fun i j => raw8001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8001step0 raw8001; decide +kernel
      have hl : raw8001step0Labels = raw8001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8001 raw8001Labels permutation346 hz
    mixedMoment B raw8001step0 raw8001step0Labels = mixedMoment B raw8001step1 raw8001step1Labels := by
      have hz : ∀ j, raw8001step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8001step1 = (fun i j => raw8001step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8001step1 raw8001step0; decide +kernel
      have hl : raw8001step1Labels = raw8001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8001step0 raw8001step0Labels permutation56 hz
    mixedMoment B raw8001step1 raw8001step1Labels = mixedMoment B raw8001step2 raw8001step2Labels := by
      have ha : raw8001step2 = (fun i j => raw8001step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8001step2 raw8001step1; decide +kernel
      have hl : raw8001step2Labels = raw8001step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8001step1 raw8001step1Labels permutation9 permutation3
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw8002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8002step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8002 raw8002Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw8002 raw8002Labels = mixedMoment B raw8002step0 raw8002step0Labels := by
      have hz : ∀ j, raw8002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8002step0 = (fun i j => raw8002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8002step0 raw8002; decide +kernel
      have hl : raw8002step0Labels = raw8002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8002 raw8002Labels permutation346 hz
    mixedMoment B raw8002step0 raw8002step0Labels = mixedMoment B raw8002step1 raw8002step1Labels := by
      have ha : raw8002step1 = (fun i j => raw8002step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8002step1 raw8002step0; decide +kernel
      have hl : raw8002step1Labels = raw8002step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8002step0 raw8002step0Labels permutation151 permutation2
    mixedMoment B raw8002step1 raw8002step1Labels = mixedMoment B raw8002step2 raw8002step2Labels := by
      have ha : raw8002step2 = -raw8002step1 := by apply Matrix.ext; change ∀ i j, raw8002step2 i j = -(raw8002step1 i j); unfold raw8002step2 raw8002step1; decide +kernel
      have hl : raw8002step2Labels = raw8002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw8003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8003step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8003 raw8003Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw8003 raw8003Labels = mixedMoment B raw8003step0 raw8003step0Labels := by
      have hz : ∀ j, raw8003 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8003step0 = (fun i j => raw8003 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8003step0 raw8003; decide +kernel
      have hl : raw8003step0Labels = raw8003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8003 raw8003Labels permutation265 hz
    mixedMoment B raw8003step0 raw8003step0Labels = mixedMoment B raw8003step1 raw8003step1Labels := by
      have ha : raw8003step1 = (fun i j => raw8003step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8003step1 raw8003step0; decide +kernel
      have hl : raw8003step1Labels = raw8003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8003step0 raw8003step0Labels permutation151 permutation2
    mixedMoment B raw8003step1 raw8003step1Labels = mixedMoment B raw8003step2 raw8003step2Labels := by
      have ha : raw8003step2 = -raw8003step1 := by apply Matrix.ext; change ∀ i j, raw8003step2 i j = -(raw8003step1 i j); unfold raw8003step2 raw8003step1; decide +kernel
      have hl : raw8003step2Labels = raw8003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw8004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8004step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8004step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8004step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw8004step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8004step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw8004step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8004 raw8004Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw8004 raw8004Labels = mixedMoment B raw8004step0 raw8004step0Labels := by
      have hz : ∀ j, raw8004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8004step0 = (fun i j => raw8004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8004step0 raw8004; decide +kernel
      have hl : raw8004step0Labels = raw8004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8004 raw8004Labels permutation346 hz
    mixedMoment B raw8004step0 raw8004step0Labels = mixedMoment B raw8004step1 raw8004step1Labels := by
      have hz : ∀ j, raw8004step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8004step1 = (fun i j => raw8004step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8004step1 raw8004step0; decide +kernel
      have hl : raw8004step1Labels = raw8004step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8004step0 raw8004step0Labels permutation56 hz
    mixedMoment B raw8004step1 raw8004step1Labels = mixedMoment B raw8004step2 raw8004step2Labels := by
      have ha : raw8004step2 = (fun i j => raw8004step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8004step2 raw8004step1; decide +kernel
      have hl : raw8004step2Labels = raw8004step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8004step1 raw8004step1Labels permutation31 permutation2
    mixedMoment B raw8004step2 raw8004step2Labels = mixedMoment B raw8004step3 raw8004step3Labels := by
      have ha : raw8004step3 = -raw8004step2 := by apply Matrix.ext; change ∀ i j, raw8004step3 i j = -(raw8004step2 i j); unfold raw8004step3 raw8004step2; decide +kernel
      have hl : raw8004step3Labels = raw8004step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw8005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8005step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw8005step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8005step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw8005step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8005step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw8005step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8005 raw8005Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw8005 raw8005Labels = mixedMoment B raw8005step0 raw8005step0Labels := by
      have hz : ∀ j, raw8005 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8005step0 = (fun i j => raw8005 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8005step0 raw8005; decide +kernel
      have hl : raw8005step0Labels = raw8005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8005 raw8005Labels permutation520 hz
    mixedMoment B raw8005step0 raw8005step0Labels = mixedMoment B raw8005step1 raw8005step1Labels := by
      have hz : ∀ j, raw8005step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8005step1 = (fun i j => raw8005step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8005step1 raw8005step0; decide +kernel
      have hl : raw8005step1Labels = raw8005step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8005step0 raw8005step0Labels permutation80 hz
    mixedMoment B raw8005step1 raw8005step1Labels = mixedMoment B raw8005step2 raw8005step2Labels := by
      have hz : ∀ j, raw8005step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw8005step2 = (fun i j => raw8005step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw8005step2 raw8005step1; decide +kernel
      have hl : raw8005step2Labels = raw8005step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8005step1 raw8005step1Labels permutation14 hz
    mixedMoment B raw8005step2 raw8005step2Labels = mixedMoment B raw8005step3 raw8005step3Labels := by
      have ha : raw8005step3 = (fun i j => raw8005step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8005step3 raw8005step2; decide +kernel
      have hl : raw8005step3Labels = raw8005step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8005step2 raw8005step2Labels permutation7 permutation2
    mixedMoment B raw8005step3 raw8005step3Labels = mixedMoment B raw8005step4 raw8005step4Labels := by
      have ha : raw8005step4 = -raw8005step3 := by apply Matrix.ext; change ∀ i j, raw8005step4 i j = -(raw8005step3 i j); unfold raw8005step4 raw8005step3; decide +kernel
      have hl : raw8005step4Labels = raw8005step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw8006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8006 raw8006Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw8006 raw8006Labels = mixedMoment B raw8006step0 raw8006step0Labels := by
      have hz : ∀ j, raw8006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8006step0 = (fun i j => raw8006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8006step0 raw8006; decide +kernel
      have hl : raw8006step0Labels = raw8006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8006 raw8006Labels permutation346 hz
    mixedMoment B raw8006step0 raw8006step0Labels = mixedMoment B raw8006step1 raw8006step1Labels := by
      have hz : ∀ j, raw8006step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8006step1 = (fun i j => raw8006step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8006step1 raw8006step0; decide +kernel
      have hl : raw8006step1Labels = raw8006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8006step0 raw8006step0Labels permutation56 hz
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw8007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8007step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8007step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8007 raw8007Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw8007 raw8007Labels = mixedMoment B raw8007step0 raw8007step0Labels := by
      have hz : ∀ j, raw8007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8007step0 = (fun i j => raw8007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8007step0 raw8007; decide +kernel
      have hl : raw8007step0Labels = raw8007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8007 raw8007Labels permutation346 hz
    mixedMoment B raw8007step0 raw8007step0Labels = mixedMoment B raw8007step1 raw8007step1Labels := by
      have ha : raw8007step1 = (fun i j => raw8007step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8007step1 raw8007step0; decide +kernel
      have hl : raw8007step1Labels = raw8007step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8007step0 raw8007step0Labels permutation38 permutation3
    mixedMoment B raw8007step1 raw8007step1Labels = mixedMoment B raw8007step2 raw8007step2Labels := by
      have ha : raw8007step2 = raw8007step1 := by apply Matrix.ext; unfold raw8007step2 raw8007step1; decide +kernel
      have hl : raw8007step1Labels = labelEmbedding6 ∘ raw8007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8007step1 raw8007step1Labels raw8007step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw8008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8008step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8008step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8008 raw8008Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw8008 raw8008Labels = mixedMoment B raw8008step0 raw8008step0Labels := by
      have ha : raw8008step0 = (fun i j => raw8008 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8008step0 raw8008; decide +kernel
      have hl : raw8008step0Labels = raw8008Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8008 raw8008Labels permutation182 permutation3
    mixedMoment B raw8008step0 raw8008step0Labels = mixedMoment B raw8008step1 raw8008step1Labels := by
      have ha : raw8008step1 = raw8008step0 := by apply Matrix.ext; unfold raw8008step1 raw8008step0; decide +kernel
      have hl : raw8008step0Labels = labelEmbedding6 ∘ raw8008step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8008step0 raw8008step0Labels raw8008step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw8009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8009step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8009step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8009 raw8009Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw8009 raw8009Labels = mixedMoment B raw8009step0 raw8009step0Labels := by
      have hz : ∀ j, raw8009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8009step0 = (fun i j => raw8009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8009step0 raw8009; decide +kernel
      have hl : raw8009step0Labels = raw8009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8009 raw8009Labels permutation346 hz
    mixedMoment B raw8009step0 raw8009step0Labels = mixedMoment B raw8009step1 raw8009step1Labels := by
      have ha : raw8009step1 = (fun i j => raw8009step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8009step1 raw8009step0; decide +kernel
      have hl : raw8009step1Labels = raw8009step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8009step0 raw8009step0Labels permutation38 permutation3
    mixedMoment B raw8009step1 raw8009step1Labels = mixedMoment B raw8009step2 raw8009step2Labels := by
      have ha : raw8009step2 = raw8009step1 := by apply Matrix.ext; unfold raw8009step2 raw8009step1; decide +kernel
      have hl : raw8009step1Labels = labelEmbedding6 ∘ raw8009step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8009step1 raw8009step1Labels raw8009step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw8010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8010step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8010step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8010step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8010step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8010step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8010 raw8010Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw8010 raw8010Labels = mixedMoment B raw8010step0 raw8010step0Labels := by
      have hz : ∀ j, raw8010 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8010step0 = (fun i j => raw8010 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8010step0 raw8010; decide +kernel
      have hl : raw8010step0Labels = raw8010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8010 raw8010Labels permutation520 hz
    mixedMoment B raw8010step0 raw8010step0Labels = mixedMoment B raw8010step1 raw8010step1Labels := by
      have hz : ∀ j, raw8010step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8010step1 = (fun i j => raw8010step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8010step1 raw8010step0; decide +kernel
      have hl : raw8010step1Labels = raw8010step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8010step0 raw8010step0Labels permutation80 hz
    mixedMoment B raw8010step1 raw8010step1Labels = mixedMoment B raw8010step2 raw8010step2Labels := by
      have ha : raw8010step2 = (fun i j => raw8010step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8010step2 raw8010step1; decide +kernel
      have hl : raw8010step2Labels = raw8010step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8010step1 raw8010step1Labels permutation10 permutation3
    mixedMoment B raw8010step2 raw8010step2Labels = mixedMoment B raw8010step3 raw8010step3Labels := by
      have ha : raw8010step3 = raw8010step2 := by apply Matrix.ext; unfold raw8010step3 raw8010step2; decide +kernel
      have hl : raw8010step2Labels = labelEmbedding6 ∘ raw8010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8010step2 raw8010step2Labels raw8010step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw8011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8011step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8011 raw8011Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw8011 raw8011Labels = mixedMoment B raw8011step0 raw8011step0Labels := by
      have hz : ∀ j, raw8011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8011step0 = (fun i j => raw8011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8011step0 raw8011; decide +kernel
      have hl : raw8011step0Labels = raw8011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8011 raw8011Labels permutation346 hz
    mixedMoment B raw8011step0 raw8011step0Labels = mixedMoment B raw8011step1 raw8011step1Labels := by
      have ha : raw8011step1 = (fun i j => raw8011step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8011step1 raw8011step0; decide +kernel
      have hl : raw8011step1Labels = raw8011step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8011step0 raw8011step0Labels permutation42 permutation3
    mixedMoment B raw8011step1 raw8011step1Labels = mixedMoment B raw8011step2 raw8011step2Labels := by
      have ha : raw8011step2 = raw8011step1 := by apply Matrix.ext; unfold raw8011step2 raw8011step1; decide +kernel
      have hl : raw8011step1Labels = labelEmbedding6 ∘ raw8011step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8011step1 raw8011step1Labels raw8011step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw8012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8012step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8012step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8012 raw8012Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw8012 raw8012Labels = mixedMoment B raw8012step0 raw8012step0Labels := by
      have hz : ∀ j, raw8012 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8012step0 = (fun i j => raw8012 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8012step0 raw8012; decide +kernel
      have hl : raw8012step0Labels = raw8012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8012 raw8012Labels permutation265 hz
    mixedMoment B raw8012step0 raw8012step0Labels = mixedMoment B raw8012step1 raw8012step1Labels := by
      have ha : raw8012step1 = (fun i j => raw8012step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8012step1 raw8012step0; decide +kernel
      have hl : raw8012step1Labels = raw8012step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8012step0 raw8012step0Labels permutation38 permutation3
    mixedMoment B raw8012step1 raw8012step1Labels = mixedMoment B raw8012step2 raw8012step2Labels := by
      have ha : raw8012step2 = raw8012step1 := by apply Matrix.ext; unfold raw8012step2 raw8012step1; decide +kernel
      have hl : raw8012step1Labels = labelEmbedding6 ∘ raw8012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8012step1 raw8012step1Labels raw8012step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw8013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8013step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8013 raw8013Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw8013 raw8013Labels = mixedMoment B raw8013step0 raw8013step0Labels := by
      have ha : raw8013step0 = (fun i j => raw8013 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8013step0 raw8013; decide +kernel
      have hl : raw8013step0Labels = raw8013Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8013 raw8013Labels permutation158 permutation3
    mixedMoment B raw8013step0 raw8013step0Labels = mixedMoment B raw8013step1 raw8013step1Labels := by
      have ha : raw8013step1 = raw8013step0 := by apply Matrix.ext; unfold raw8013step1 raw8013step0; decide +kernel
      have hl : raw8013step0Labels = labelEmbedding6 ∘ raw8013step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8013step0 raw8013step0Labels raw8013step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw8014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8014step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8014step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8014 raw8014Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw8014 raw8014Labels = mixedMoment B raw8014step0 raw8014step0Labels := by
      have hz : ∀ j, raw8014 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8014step0 = (fun i j => raw8014 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8014step0 raw8014; decide +kernel
      have hl : raw8014step0Labels = raw8014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8014 raw8014Labels permutation265 hz
    mixedMoment B raw8014step0 raw8014step0Labels = mixedMoment B raw8014step1 raw8014step1Labels := by
      have ha : raw8014step1 = (fun i j => raw8014step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8014step1 raw8014step0; decide +kernel
      have hl : raw8014step1Labels = raw8014step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8014step0 raw8014step0Labels permutation38 permutation3
    mixedMoment B raw8014step1 raw8014step1Labels = mixedMoment B raw8014step2 raw8014step2Labels := by
      have ha : raw8014step2 = raw8014step1 := by apply Matrix.ext; unfold raw8014step2 raw8014step1; decide +kernel
      have hl : raw8014step1Labels = labelEmbedding6 ∘ raw8014step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8014step1 raw8014step1Labels raw8014step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw8015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8015step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8015step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8015step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8015 raw8015Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw8015 raw8015Labels = mixedMoment B raw8015step0 raw8015step0Labels := by
      have hz : ∀ j, raw8015 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8015step0 = (fun i j => raw8015 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8015step0 raw8015; decide +kernel
      have hl : raw8015step0Labels = raw8015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8015 raw8015Labels permutation520 hz
    mixedMoment B raw8015step0 raw8015step0Labels = mixedMoment B raw8015step1 raw8015step1Labels := by
      have hz : ∀ j, raw8015step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8015step1 = (fun i j => raw8015step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8015step1 raw8015step0; decide +kernel
      have hl : raw8015step1Labels = raw8015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8015step0 raw8015step0Labels permutation56 hz
    mixedMoment B raw8015step1 raw8015step1Labels = mixedMoment B raw8015step2 raw8015step2Labels := by
      have ha : raw8015step2 = (fun i j => raw8015step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8015step2 raw8015step1; decide +kernel
      have hl : raw8015step2Labels = raw8015step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8015step1 raw8015step1Labels permutation10 permutation3
    mixedMoment B raw8015step2 raw8015step2Labels = mixedMoment B raw8015step3 raw8015step3Labels := by
      have ha : raw8015step3 = raw8015step2 := by apply Matrix.ext; unfold raw8015step3 raw8015step2; decide +kernel
      have hl : raw8015step2Labels = labelEmbedding6 ∘ raw8015step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8015step2 raw8015step2Labels raw8015step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw8016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8016 raw8016Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw8016 raw8016Labels = mixedMoment B raw8016step0 raw8016step0Labels := by
      have hz : ∀ j, raw8016 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8016step0 = (fun i j => raw8016 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8016step0 raw8016; decide +kernel
      have hl : raw8016step0Labels = raw8016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8016 raw8016Labels permutation265 hz
    mixedMoment B raw8016step0 raw8016step0Labels = mixedMoment B raw8016step1 raw8016step1Labels := by
      have ha : raw8016step1 = (fun i j => raw8016step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8016step1 raw8016step0; decide +kernel
      have hl : raw8016step1Labels = raw8016step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8016step0 raw8016step0Labels permutation42 permutation3
    mixedMoment B raw8016step1 raw8016step1Labels = mixedMoment B raw8016step2 raw8016step2Labels := by
      have ha : raw8016step2 = raw8016step1 := by apply Matrix.ext; unfold raw8016step2 raw8016step1; decide +kernel
      have hl : raw8016step1Labels = labelEmbedding6 ∘ raw8016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8016step1 raw8016step1Labels raw8016step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw8017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8017step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8017 raw8017Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw8017 raw8017Labels = mixedMoment B raw8017step0 raw8017step0Labels := by
      have hz : ∀ j, raw8017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8017step0 = (fun i j => raw8017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8017step0 raw8017; decide +kernel
      have hl : raw8017step0Labels = raw8017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8017 raw8017Labels permutation346 hz
    mixedMoment B raw8017step0 raw8017step0Labels = mixedMoment B raw8017step1 raw8017step1Labels := by
      have hz : ∀ j, raw8017step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8017step1 = (fun i j => raw8017step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8017step1 raw8017step0; decide +kernel
      have hl : raw8017step1Labels = raw8017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8017step0 raw8017step0Labels permutation56 hz
    mixedMoment B raw8017step1 raw8017step1Labels = mixedMoment B raw8017step2 raw8017step2Labels := by
      have ha : raw8017step2 = (fun i j => raw8017step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8017step2 raw8017step1; decide +kernel
      have hl : raw8017step2Labels = raw8017step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8017step1 raw8017step1Labels permutation10 permutation3
    mixedMoment B raw8017step2 raw8017step2Labels = mixedMoment B raw8017step3 raw8017step3Labels := by
      have ha : raw8017step3 = raw8017step2 := by apply Matrix.ext; unfold raw8017step3 raw8017step2; decide +kernel
      have hl : raw8017step2Labels = labelEmbedding6 ∘ raw8017step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8017step2 raw8017step2Labels raw8017step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw8018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8018step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8018step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8018 raw8018Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw8018 raw8018Labels = mixedMoment B raw8018step0 raw8018step0Labels := by
      have hz : ∀ j, raw8018 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8018step0 = (fun i j => raw8018 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8018step0 raw8018; decide +kernel
      have hl : raw8018step0Labels = raw8018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8018 raw8018Labels permutation346 hz
    mixedMoment B raw8018step0 raw8018step0Labels = mixedMoment B raw8018step1 raw8018step1Labels := by
      have ha : raw8018step1 = (fun i j => raw8018step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8018step1 raw8018step0; decide +kernel
      have hl : raw8018step1Labels = raw8018step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8018step0 raw8018step0Labels permutation34 permutation3
    mixedMoment B raw8018step1 raw8018step1Labels = mixedMoment B raw8018step2 raw8018step2Labels := by
      have ha : raw8018step2 = raw8018step1 := by apply Matrix.ext; unfold raw8018step2 raw8018step1; decide +kernel
      have hl : raw8018step1Labels = labelEmbedding6 ∘ raw8018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8018step1 raw8018step1Labels raw8018step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw8019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8019step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8019step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8019 raw8019Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw8019 raw8019Labels = mixedMoment B raw8019step0 raw8019step0Labels := by
      have hz : ∀ j, raw8019 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8019step0 = (fun i j => raw8019 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8019step0 raw8019; decide +kernel
      have hl : raw8019step0Labels = raw8019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8019 raw8019Labels permutation265 hz
    mixedMoment B raw8019step0 raw8019step0Labels = mixedMoment B raw8019step1 raw8019step1Labels := by
      have ha : raw8019step1 = (fun i j => raw8019step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8019step1 raw8019step0; decide +kernel
      have hl : raw8019step1Labels = raw8019step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8019step0 raw8019step0Labels permutation34 permutation3
    mixedMoment B raw8019step1 raw8019step1Labels = mixedMoment B raw8019step2 raw8019step2Labels := by
      have ha : raw8019step2 = raw8019step1 := by apply Matrix.ext; unfold raw8019step2 raw8019step1; decide +kernel
      have hl : raw8019step1Labels = labelEmbedding6 ∘ raw8019step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8019step1 raw8019step1Labels raw8019step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw8020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw8020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw8020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8020step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw8020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8020step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw8020step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8020step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw8020step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8020 raw8020Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw8020 raw8020Labels = mixedMoment B raw8020step0 raw8020step0Labels := by
      have hz : ∀ j, raw8020 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8020step0 = (fun i j => raw8020 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8020step0 raw8020; decide +kernel
      have hl : raw8020step0Labels = raw8020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8020 raw8020Labels permutation520 hz
    mixedMoment B raw8020step0 raw8020step0Labels = mixedMoment B raw8020step1 raw8020step1Labels := by
      have hz : ∀ j, raw8020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8020step1 = (fun i j => raw8020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8020step1 raw8020step0; decide +kernel
      have hl : raw8020step1Labels = raw8020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8020step0 raw8020step0Labels permutation80 hz
    mixedMoment B raw8020step1 raw8020step1Labels = mixedMoment B raw8020step2 raw8020step2Labels := by
      have hz : ∀ j, raw8020step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw8020step2 = (fun i j => raw8020step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw8020step2 raw8020step1; decide +kernel
      have hl : raw8020step2Labels = raw8020step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8020step1 raw8020step1Labels permutation14 hz
    mixedMoment B raw8020step2 raw8020step2Labels = mixedMoment B raw8020step3 raw8020step3Labels := by
      have ha : raw8020step3 = (fun i j => raw8020step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8020step3 raw8020step2; decide +kernel
      have hl : raw8020step3Labels = raw8020step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8020step2 raw8020step2Labels permutation2 permutation3
    mixedMoment B raw8020step3 raw8020step3Labels = mixedMoment B raw8020step4 raw8020step4Labels := by
      have ha : raw8020step4 = raw8020step3 := by apply Matrix.ext; unfold raw8020step4 raw8020step3; decide +kernel
      have hl : raw8020step3Labels = labelEmbedding6 ∘ raw8020step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8020step3 raw8020step3Labels raw8020step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw8021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8021step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8021step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8021step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8021step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8021 raw8021Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw8021 raw8021Labels = mixedMoment B raw8021step0 raw8021step0Labels := by
      have hz : ∀ j, raw8021 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8021step0 = (fun i j => raw8021 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8021step0 raw8021; decide +kernel
      have hl : raw8021step0Labels = raw8021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8021 raw8021Labels permutation346 hz
    mixedMoment B raw8021step0 raw8021step0Labels = mixedMoment B raw8021step1 raw8021step1Labels := by
      have hz : ∀ j, raw8021step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8021step1 = (fun i j => raw8021step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8021step1 raw8021step0; decide +kernel
      have hl : raw8021step1Labels = raw8021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8021step0 raw8021step0Labels permutation56 hz
    mixedMoment B raw8021step1 raw8021step1Labels = mixedMoment B raw8021step2 raw8021step2Labels := by
      have ha : raw8021step2 = (fun i j => raw8021step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8021step2 raw8021step1; decide +kernel
      have hl : raw8021step2Labels = raw8021step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8021step1 raw8021step1Labels permutation13 permutation3
    mixedMoment B raw8021step2 raw8021step2Labels = mixedMoment B raw8021step3 raw8021step3Labels := by
      have ha : raw8021step3 = raw8021step2 := by apply Matrix.ext; unfold raw8021step3 raw8021step2; decide +kernel
      have hl : raw8021step2Labels = labelEmbedding6 ∘ raw8021step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8021step2 raw8021step2Labels raw8021step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw8022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8022step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8022step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8022step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8022step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8022step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8022 raw8022Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw8022 raw8022Labels = mixedMoment B raw8022step0 raw8022step0Labels := by
      have hz : ∀ j, raw8022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8022step0 = (fun i j => raw8022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8022step0 raw8022; decide +kernel
      have hl : raw8022step0Labels = raw8022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8022 raw8022Labels permutation346 hz
    mixedMoment B raw8022step0 raw8022step0Labels = mixedMoment B raw8022step1 raw8022step1Labels := by
      have hz : ∀ j, raw8022step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8022step1 = (fun i j => raw8022step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8022step1 raw8022step0; decide +kernel
      have hl : raw8022step1Labels = raw8022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8022step0 raw8022step0Labels permutation56 hz
    mixedMoment B raw8022step1 raw8022step1Labels = mixedMoment B raw8022step2 raw8022step2Labels := by
      have ha : raw8022step2 = (fun i j => raw8022step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8022step2 raw8022step1; decide +kernel
      have hl : raw8022step2Labels = raw8022step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8022step1 raw8022step1Labels permutation9 permutation3
    mixedMoment B raw8022step2 raw8022step2Labels = mixedMoment B raw8022step3 raw8022step3Labels := by
      have ha : raw8022step3 = raw8022step2 := by apply Matrix.ext; unfold raw8022step3 raw8022step2; decide +kernel
      have hl : raw8022step2Labels = labelEmbedding6 ∘ raw8022step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8022step2 raw8022step2Labels raw8022step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw8023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8023step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8023step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8023 raw8023Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw8023 raw8023Labels = mixedMoment B raw8023step0 raw8023step0Labels := by
      have hz : ∀ j, raw8023 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8023step0 = (fun i j => raw8023 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8023step0 raw8023; decide +kernel
      have hl : raw8023step0Labels = raw8023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8023 raw8023Labels permutation346 hz
    mixedMoment B raw8023step0 raw8023step0Labels = mixedMoment B raw8023step1 raw8023step1Labels := by
      have ha : raw8023step1 = (fun i j => raw8023step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8023step1 raw8023step0; decide +kernel
      have hl : raw8023step1Labels = raw8023step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8023step0 raw8023step0Labels permutation33 permutation3
    mixedMoment B raw8023step1 raw8023step1Labels = mixedMoment B raw8023step2 raw8023step2Labels := by
      have ha : raw8023step2 = raw8023step1 := by apply Matrix.ext; unfold raw8023step2 raw8023step1; decide +kernel
      have hl : raw8023step1Labels = labelEmbedding6 ∘ raw8023step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8023step1 raw8023step1Labels raw8023step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw8024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8024step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8024step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8024 raw8024Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw8024 raw8024Labels = mixedMoment B raw8024step0 raw8024step0Labels := by
      have hz : ∀ j, raw8024 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8024step0 = (fun i j => raw8024 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8024step0 raw8024; decide +kernel
      have hl : raw8024step0Labels = raw8024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8024 raw8024Labels permutation265 hz
    mixedMoment B raw8024step0 raw8024step0Labels = mixedMoment B raw8024step1 raw8024step1Labels := by
      have ha : raw8024step1 = (fun i j => raw8024step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8024step1 raw8024step0; decide +kernel
      have hl : raw8024step1Labels = raw8024step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8024step0 raw8024step0Labels permutation33 permutation3
    mixedMoment B raw8024step1 raw8024step1Labels = mixedMoment B raw8024step2 raw8024step2Labels := by
      have ha : raw8024step2 = raw8024step1 := by apply Matrix.ext; unfold raw8024step2 raw8024step1; decide +kernel
      have hl : raw8024step1Labels = labelEmbedding6 ∘ raw8024step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8024step1 raw8024step1Labels raw8024step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw8025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8025step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw8025step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8025step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw8025step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8025 raw8025Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw8025 raw8025Labels = mixedMoment B raw8025step0 raw8025step0Labels := by
      have hz : ∀ j, raw8025 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8025step0 = (fun i j => raw8025 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8025step0 raw8025; decide +kernel
      have hl : raw8025step0Labels = raw8025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8025 raw8025Labels permutation346 hz
    mixedMoment B raw8025step0 raw8025step0Labels = mixedMoment B raw8025step1 raw8025step1Labels := by
      have hz : ∀ j, raw8025step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8025step1 = (fun i j => raw8025step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8025step1 raw8025step0; decide +kernel
      have hl : raw8025step1Labels = raw8025step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8025step0 raw8025step0Labels permutation56 hz
    mixedMoment B raw8025step1 raw8025step1Labels = mixedMoment B raw8025step2 raw8025step2Labels := by
      have ha : raw8025step2 = (fun i j => raw8025step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8025step2 raw8025step1; decide +kernel
      have hl : raw8025step2Labels = raw8025step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8025step1 raw8025step1Labels permutation9 permutation3
    mixedMoment B raw8025step2 raw8025step2Labels = mixedMoment B raw8025step3 raw8025step3Labels := by
      have ha : raw8025step3 = raw8025step2 := by apply Matrix.ext; unfold raw8025step3 raw8025step2; decide +kernel
      have hl : raw8025step2Labels = labelEmbedding6 ∘ raw8025step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8025step2 raw8025step2Labels raw8025step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw8026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw8026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw8026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw8026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8026step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8026step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8026step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8026 raw8026Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw8026 raw8026Labels = mixedMoment B raw8026step0 raw8026step0Labels := by
      have hz : ∀ j, raw8026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8026step0 = (fun i j => raw8026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8026step0 raw8026; decide +kernel
      have hl : raw8026step0Labels = raw8026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8026 raw8026Labels permutation346 hz
    mixedMoment B raw8026step0 raw8026step0Labels = mixedMoment B raw8026step1 raw8026step1Labels := by
      have hz : ∀ j, raw8026step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8026step1 = (fun i j => raw8026step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8026step1 raw8026step0; decide +kernel
      have hl : raw8026step1Labels = raw8026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8026step0 raw8026step0Labels permutation56 hz
    mixedMoment B raw8026step1 raw8026step1Labels = mixedMoment B raw8026step2 raw8026step2Labels := by
      have ha : raw8026step2 = (fun i j => raw8026step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8026step2 raw8026step1; decide +kernel
      have hl : raw8026step2Labels = raw8026step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8026step1 raw8026step1Labels permutation9 permutation3
    mixedMoment B raw8026step2 raw8026step2Labels = mixedMoment B raw8026step3 raw8026step3Labels := by
      have ha : raw8026step3 = raw8026step2 := by apply Matrix.ext; unfold raw8026step3 raw8026step2; decide +kernel
      have hl : raw8026step2Labels = labelEmbedding6 ∘ raw8026step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8026step2 raw8026step2Labels raw8026step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw8027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8027step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8027step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8027step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8027 raw8027Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw8027 raw8027Labels = mixedMoment B raw8027step0 raw8027step0Labels := by
      have hz : ∀ j, raw8027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8027step0 = (fun i j => raw8027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8027step0 raw8027; decide +kernel
      have hl : raw8027step0Labels = raw8027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8027 raw8027Labels permutation346 hz
    mixedMoment B raw8027step0 raw8027step0Labels = mixedMoment B raw8027step1 raw8027step1Labels := by
      have hz : ∀ j, raw8027step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8027step1 = (fun i j => raw8027step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8027step1 raw8027step0; decide +kernel
      have hl : raw8027step1Labels = raw8027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8027step0 raw8027step0Labels permutation56 hz
    mixedMoment B raw8027step1 raw8027step1Labels = mixedMoment B raw8027step2 raw8027step2Labels := by
      have ha : raw8027step2 = (fun i j => raw8027step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8027step2 raw8027step1; decide +kernel
      have hl : raw8027step2Labels = raw8027step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8027step1 raw8027step1Labels permutation8 permutation3
    mixedMoment B raw8027step2 raw8027step2Labels = mixedMoment B raw8027step3 raw8027step3Labels := by
      have ha : raw8027step3 = raw8027step2 := by apply Matrix.ext; unfold raw8027step3 raw8027step2; decide +kernel
      have hl : raw8027step2Labels = labelEmbedding6 ∘ raw8027step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8027step2 raw8027step2Labels raw8027step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw8028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8028step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8028 raw8028Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw8028 raw8028Labels = mixedMoment B raw8028step0 raw8028step0Labels := by
      have hz : ∀ j, raw8028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8028step0 = (fun i j => raw8028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8028step0 raw8028; decide +kernel
      have hl : raw8028step0Labels = raw8028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8028 raw8028Labels permutation346 hz
    mixedMoment B raw8028step0 raw8028step0Labels = mixedMoment B raw8028step1 raw8028step1Labels := by
      have ha : raw8028step1 = (fun i j => raw8028step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8028step1 raw8028step0; decide +kernel
      have hl : raw8028step1Labels = raw8028step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8028step0 raw8028step0Labels permutation32 permutation3
    mixedMoment B raw8028step1 raw8028step1Labels = mixedMoment B raw8028step2 raw8028step2Labels := by
      have ha : raw8028step2 = raw8028step1 := by apply Matrix.ext; unfold raw8028step2 raw8028step1; decide +kernel
      have hl : raw8028step1Labels = labelEmbedding6 ∘ raw8028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8028step1 raw8028step1Labels raw8028step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw8029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8029step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8029 raw8029Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw8029 raw8029Labels = mixedMoment B raw8029step0 raw8029step0Labels := by
      have hz : ∀ j, raw8029 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8029step0 = (fun i j => raw8029 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8029step0 raw8029; decide +kernel
      have hl : raw8029step0Labels = raw8029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8029 raw8029Labels permutation265 hz
    mixedMoment B raw8029step0 raw8029step0Labels = mixedMoment B raw8029step1 raw8029step1Labels := by
      have ha : raw8029step1 = (fun i j => raw8029step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8029step1 raw8029step0; decide +kernel
      have hl : raw8029step1Labels = raw8029step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8029step0 raw8029step0Labels permutation32 permutation3
    mixedMoment B raw8029step1 raw8029step1Labels = mixedMoment B raw8029step2 raw8029step2Labels := by
      have ha : raw8029step2 = raw8029step1 := by apply Matrix.ext; unfold raw8029step2 raw8029step1; decide +kernel
      have hl : raw8029step1Labels = labelEmbedding6 ∘ raw8029step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8029step1 raw8029step1Labels raw8029step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw8030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8030step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8030step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw8030step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8030step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw8030step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8030 raw8030Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw8030 raw8030Labels = mixedMoment B raw8030step0 raw8030step0Labels := by
      have hz : ∀ j, raw8030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8030step0 = (fun i j => raw8030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8030step0 raw8030; decide +kernel
      have hl : raw8030step0Labels = raw8030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8030 raw8030Labels permutation346 hz
    mixedMoment B raw8030step0 raw8030step0Labels = mixedMoment B raw8030step1 raw8030step1Labels := by
      have hz : ∀ j, raw8030step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8030step1 = (fun i j => raw8030step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8030step1 raw8030step0; decide +kernel
      have hl : raw8030step1Labels = raw8030step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8030step0 raw8030step0Labels permutation56 hz
    mixedMoment B raw8030step1 raw8030step1Labels = mixedMoment B raw8030step2 raw8030step2Labels := by
      have ha : raw8030step2 = (fun i j => raw8030step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8030step2 raw8030step1; decide +kernel
      have hl : raw8030step2Labels = raw8030step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8030step1 raw8030step1Labels permutation31 permutation2
    mixedMoment B raw8030step2 raw8030step2Labels = mixedMoment B raw8030step3 raw8030step3Labels := by
      have ha : raw8030step3 = -raw8030step2 := by apply Matrix.ext; change ∀ i j, raw8030step3 i j = -(raw8030step2 i j); unfold raw8030step3 raw8030step2; decide +kernel
      have hl : raw8030step3Labels = raw8030step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5174 node5174Labels := by rfl

def raw8031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw8031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw8031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw8031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8031step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![3, -1, -2]]
def raw8031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8031step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw8031step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8031step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw8031step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8031 raw8031Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw8031 raw8031Labels = mixedMoment B raw8031step0 raw8031step0Labels := by
      have hz : ∀ j, raw8031 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8031step0 = (fun i j => raw8031 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8031step0 raw8031; decide +kernel
      have hl : raw8031step0Labels = raw8031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8031 raw8031Labels permutation520 hz
    mixedMoment B raw8031step0 raw8031step0Labels = mixedMoment B raw8031step1 raw8031step1Labels := by
      have hz : ∀ j, raw8031step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8031step1 = (fun i j => raw8031step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8031step1 raw8031step0; decide +kernel
      have hl : raw8031step1Labels = raw8031step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8031step0 raw8031step0Labels permutation80 hz
    mixedMoment B raw8031step1 raw8031step1Labels = mixedMoment B raw8031step2 raw8031step2Labels := by
      have hz : ∀ j, raw8031step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw8031step2 = (fun i j => raw8031step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw8031step2 raw8031step1; decide +kernel
      have hl : raw8031step2Labels = raw8031step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8031step1 raw8031step1Labels permutation14 hz
    mixedMoment B raw8031step2 raw8031step2Labels = mixedMoment B raw8031step3 raw8031step3Labels := by
      have ha : raw8031step3 = (fun i j => raw8031step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8031step3 raw8031step2; decide +kernel
      have hl : raw8031step3Labels = raw8031step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8031step2 raw8031step2Labels permutation7 permutation2
    mixedMoment B raw8031step3 raw8031step3Labels = mixedMoment B raw8031step4 raw8031step4Labels := by
      have ha : raw8031step4 = -raw8031step3 := by apply Matrix.ext; change ∀ i j, raw8031step4 i j = -(raw8031step3 i j); unfold raw8031step4 raw8031step3; decide +kernel
      have hl : raw8031step4Labels = raw8031step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw8032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8032step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8032 raw8032Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw8032 raw8032Labels = mixedMoment B raw8032step0 raw8032step0Labels := by
      have hz : ∀ j, raw8032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8032step0 = (fun i j => raw8032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8032step0 raw8032; decide +kernel
      have hl : raw8032step0Labels = raw8032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8032 raw8032Labels permutation346 hz
    mixedMoment B raw8032step0 raw8032step0Labels = mixedMoment B raw8032step1 raw8032step1Labels := by
      have ha : raw8032step1 = (fun i j => raw8032step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8032step1 raw8032step0; decide +kernel
      have hl : raw8032step1Labels = raw8032step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8032step0 raw8032step0Labels permutation32 permutation3
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw8033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8033step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8033 raw8033Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw8033 raw8033Labels = mixedMoment B raw8033step0 raw8033step0Labels := by
      have hz : ∀ j, raw8033 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8033step0 = (fun i j => raw8033 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8033step0 raw8033; decide +kernel
      have hl : raw8033step0Labels = raw8033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8033 raw8033Labels permutation265 hz
    mixedMoment B raw8033step0 raw8033step0Labels = mixedMoment B raw8033step1 raw8033step1Labels := by
      have ha : raw8033step1 = (fun i j => raw8033step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8033step1 raw8033step0; decide +kernel
      have hl : raw8033step1Labels = raw8033step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8033step0 raw8033step0Labels permutation32 permutation3
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw8034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8034step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8034step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8034 raw8034Labels = mixedMoment B node4001 node4001Labels := by
  calc
    mixedMoment B raw8034 raw8034Labels = mixedMoment B raw8034step0 raw8034step0Labels := by
      have hz : ∀ j, raw8034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8034step0 = (fun i j => raw8034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8034step0 raw8034; decide +kernel
      have hl : raw8034step0Labels = raw8034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8034 raw8034Labels permutation346 hz
    mixedMoment B raw8034step0 raw8034step0Labels = mixedMoment B raw8034step1 raw8034step1Labels := by
      have hz : ∀ j, raw8034step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8034step1 = (fun i j => raw8034step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8034step1 raw8034step0; decide +kernel
      have hl : raw8034step1Labels = raw8034step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8034step0 raw8034step0Labels permutation56 hz
    mixedMoment B raw8034step1 raw8034step1Labels = mixedMoment B raw8034step2 raw8034step2Labels := by
      have ha : raw8034step2 = (fun i j => raw8034step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8034step2 raw8034step1; decide +kernel
      have hl : raw8034step2Labels = raw8034step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8034step1 raw8034step1Labels permutation8 permutation3
    _ = mixedMoment B node4001 node4001Labels := by rfl

def raw8035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8035step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8035step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8035step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw8035step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8035step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw8035step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8035 raw8035Labels = mixedMoment B node4019 node4019Labels := by
  calc
    mixedMoment B raw8035 raw8035Labels = mixedMoment B raw8035step0 raw8035step0Labels := by
      have hz : ∀ j, raw8035 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8035step0 = (fun i j => raw8035 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8035step0 raw8035; decide +kernel
      have hl : raw8035step0Labels = raw8035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8035 raw8035Labels permutation520 hz
    mixedMoment B raw8035step0 raw8035step0Labels = mixedMoment B raw8035step1 raw8035step1Labels := by
      have hz : ∀ j, raw8035step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8035step1 = (fun i j => raw8035step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8035step1 raw8035step0; decide +kernel
      have hl : raw8035step1Labels = raw8035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8035step0 raw8035step0Labels permutation80 hz
    mixedMoment B raw8035step1 raw8035step1Labels = mixedMoment B raw8035step2 raw8035step2Labels := by
      have hz : ∀ j, raw8035step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw8035step2 = (fun i j => raw8035step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw8035step2 raw8035step1; decide +kernel
      have hl : raw8035step2Labels = raw8035step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8035step1 raw8035step1Labels permutation14 hz
    mixedMoment B raw8035step2 raw8035step2Labels = mixedMoment B raw8035step3 raw8035step3Labels := by
      have ha : raw8035step3 = (fun i j => raw8035step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8035step3 raw8035step2; decide +kernel
      have hl : raw8035step3Labels = raw8035step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8035step2 raw8035step2Labels permutation2 permutation3
    _ = mixedMoment B node4019 node4019Labels := by rfl

def raw8036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8036step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8036step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8036 raw8036Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw8036 raw8036Labels = mixedMoment B raw8036step0 raw8036step0Labels := by
      have hz : ∀ j, raw8036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8036step0 = (fun i j => raw8036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8036step0 raw8036; decide +kernel
      have hl : raw8036step0Labels = raw8036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8036 raw8036Labels permutation346 hz
    mixedMoment B raw8036step0 raw8036step0Labels = mixedMoment B raw8036step1 raw8036step1Labels := by
      have hz : ∀ j, raw8036step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8036step1 = (fun i j => raw8036step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8036step1 raw8036step0; decide +kernel
      have hl : raw8036step1Labels = raw8036step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8036step0 raw8036step0Labels permutation56 hz
    mixedMoment B raw8036step1 raw8036step1Labels = mixedMoment B raw8036step2 raw8036step2Labels := by
      have ha : raw8036step2 = (fun i j => raw8036step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8036step2 raw8036step1; decide +kernel
      have hl : raw8036step2Labels = raw8036step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8036step1 raw8036step1Labels permutation9 permutation3
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw8037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8037step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8037 raw8037Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw8037 raw8037Labels = mixedMoment B raw8037step0 raw8037step0Labels := by
      have hz : ∀ j, raw8037 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8037step0 = (fun i j => raw8037 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8037step0 raw8037; decide +kernel
      have hl : raw8037step0Labels = raw8037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8037 raw8037Labels permutation346 hz
    mixedMoment B raw8037step0 raw8037step0Labels = mixedMoment B raw8037step1 raw8037step1Labels := by
      have ha : raw8037step1 = (fun i j => raw8037step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8037step1 raw8037step0; decide +kernel
      have hl : raw8037step1Labels = raw8037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8037step0 raw8037step0Labels permutation38 permutation3
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw8038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8038 raw8038Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw8038 raw8038Labels = mixedMoment B raw8038step0 raw8038step0Labels := by
      have ha : raw8038step0 = (fun i j => raw8038 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8038step0 raw8038; decide +kernel
      have hl : raw8038step0Labels = raw8038Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8038 raw8038Labels permutation182 permutation3
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw8039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8039step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8039 raw8039Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw8039 raw8039Labels = mixedMoment B raw8039step0 raw8039step0Labels := by
      have hz : ∀ j, raw8039 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8039step0 = (fun i j => raw8039 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8039step0 raw8039; decide +kernel
      have hl : raw8039step0Labels = raw8039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8039 raw8039Labels permutation346 hz
    mixedMoment B raw8039step0 raw8039step0Labels = mixedMoment B raw8039step1 raw8039step1Labels := by
      have ha : raw8039step1 = (fun i j => raw8039step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8039step1 raw8039step0; decide +kernel
      have hl : raw8039step1Labels = raw8039step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8039step0 raw8039step0Labels permutation38 permutation3
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw8040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8040step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8040step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8040step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8040 raw8040Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw8040 raw8040Labels = mixedMoment B raw8040step0 raw8040step0Labels := by
      have hz : ∀ j, raw8040 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8040step0 = (fun i j => raw8040 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8040step0 raw8040; decide +kernel
      have hl : raw8040step0Labels = raw8040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8040 raw8040Labels permutation520 hz
    mixedMoment B raw8040step0 raw8040step0Labels = mixedMoment B raw8040step1 raw8040step1Labels := by
      have hz : ∀ j, raw8040step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8040step1 = (fun i j => raw8040step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8040step1 raw8040step0; decide +kernel
      have hl : raw8040step1Labels = raw8040step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8040step0 raw8040step0Labels permutation80 hz
    mixedMoment B raw8040step1 raw8040step1Labels = mixedMoment B raw8040step2 raw8040step2Labels := by
      have ha : raw8040step2 = (fun i j => raw8040step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8040step2 raw8040step1; decide +kernel
      have hl : raw8040step2Labels = raw8040step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8040step1 raw8040step1Labels permutation10 permutation3
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw8041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8041step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8041 raw8041Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw8041 raw8041Labels = mixedMoment B raw8041step0 raw8041step0Labels := by
      have hz : ∀ j, raw8041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8041step0 = (fun i j => raw8041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8041step0 raw8041; decide +kernel
      have hl : raw8041step0Labels = raw8041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8041 raw8041Labels permutation346 hz
    mixedMoment B raw8041step0 raw8041step0Labels = mixedMoment B raw8041step1 raw8041step1Labels := by
      have ha : raw8041step1 = (fun i j => raw8041step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8041step1 raw8041step0; decide +kernel
      have hl : raw8041step1Labels = raw8041step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8041step0 raw8041step0Labels permutation42 permutation3
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw8042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8042 raw8042Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw8042 raw8042Labels = mixedMoment B raw8042step0 raw8042step0Labels := by
      have hz : ∀ j, raw8042 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8042step0 = (fun i j => raw8042 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8042step0 raw8042; decide +kernel
      have hl : raw8042step0Labels = raw8042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8042 raw8042Labels permutation265 hz
    mixedMoment B raw8042step0 raw8042step0Labels = mixedMoment B raw8042step1 raw8042step1Labels := by
      have ha : raw8042step1 = (fun i j => raw8042step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8042step1 raw8042step0; decide +kernel
      have hl : raw8042step1Labels = raw8042step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8042step0 raw8042step0Labels permutation38 permutation3
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw8043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8043 raw8043Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw8043 raw8043Labels = mixedMoment B raw8043step0 raw8043step0Labels := by
      have ha : raw8043step0 = (fun i j => raw8043 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8043step0 raw8043; decide +kernel
      have hl : raw8043step0Labels = raw8043Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8043 raw8043Labels permutation158 permutation3
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw8044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8044step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8044 raw8044Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw8044 raw8044Labels = mixedMoment B raw8044step0 raw8044step0Labels := by
      have hz : ∀ j, raw8044 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8044step0 = (fun i j => raw8044 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8044step0 raw8044; decide +kernel
      have hl : raw8044step0Labels = raw8044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8044 raw8044Labels permutation265 hz
    mixedMoment B raw8044step0 raw8044step0Labels = mixedMoment B raw8044step1 raw8044step1Labels := by
      have ha : raw8044step1 = (fun i j => raw8044step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8044step1 raw8044step0; decide +kernel
      have hl : raw8044step1Labels = raw8044step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8044step0 raw8044step0Labels permutation38 permutation3
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw8045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8045step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8045step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8045step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8045step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8045 raw8045Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw8045 raw8045Labels = mixedMoment B raw8045step0 raw8045step0Labels := by
      have hz : ∀ j, raw8045 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8045step0 = (fun i j => raw8045 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8045step0 raw8045; decide +kernel
      have hl : raw8045step0Labels = raw8045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8045 raw8045Labels permutation520 hz
    mixedMoment B raw8045step0 raw8045step0Labels = mixedMoment B raw8045step1 raw8045step1Labels := by
      have hz : ∀ j, raw8045step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8045step1 = (fun i j => raw8045step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8045step1 raw8045step0; decide +kernel
      have hl : raw8045step1Labels = raw8045step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8045step0 raw8045step0Labels permutation56 hz
    mixedMoment B raw8045step1 raw8045step1Labels = mixedMoment B raw8045step2 raw8045step2Labels := by
      have ha : raw8045step2 = (fun i j => raw8045step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8045step2 raw8045step1; decide +kernel
      have hl : raw8045step2Labels = raw8045step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8045step1 raw8045step1Labels permutation10 permutation3
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw8046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8046step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8046 raw8046Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw8046 raw8046Labels = mixedMoment B raw8046step0 raw8046step0Labels := by
      have hz : ∀ j, raw8046 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8046step0 = (fun i j => raw8046 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8046step0 raw8046; decide +kernel
      have hl : raw8046step0Labels = raw8046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8046 raw8046Labels permutation265 hz
    mixedMoment B raw8046step0 raw8046step0Labels = mixedMoment B raw8046step1 raw8046step1Labels := by
      have ha : raw8046step1 = (fun i j => raw8046step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8046step1 raw8046step0; decide +kernel
      have hl : raw8046step1Labels = raw8046step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8046step0 raw8046step0Labels permutation42 permutation3
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw8047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8047step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8047 raw8047Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw8047 raw8047Labels = mixedMoment B raw8047step0 raw8047step0Labels := by
      have hz : ∀ j, raw8047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8047step0 = (fun i j => raw8047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8047step0 raw8047; decide +kernel
      have hl : raw8047step0Labels = raw8047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8047 raw8047Labels permutation346 hz
    mixedMoment B raw8047step0 raw8047step0Labels = mixedMoment B raw8047step1 raw8047step1Labels := by
      have hz : ∀ j, raw8047step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8047step1 = (fun i j => raw8047step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8047step1 raw8047step0; decide +kernel
      have hl : raw8047step1Labels = raw8047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8047step0 raw8047step0Labels permutation56 hz
    mixedMoment B raw8047step1 raw8047step1Labels = mixedMoment B raw8047step2 raw8047step2Labels := by
      have ha : raw8047step2 = (fun i j => raw8047step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8047step2 raw8047step1; decide +kernel
      have hl : raw8047step2Labels = raw8047step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8047step1 raw8047step1Labels permutation10 permutation3
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw8048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8048step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8048 raw8048Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw8048 raw8048Labels = mixedMoment B raw8048step0 raw8048step0Labels := by
      have hz : ∀ j, raw8048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8048step0 = (fun i j => raw8048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8048step0 raw8048; decide +kernel
      have hl : raw8048step0Labels = raw8048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8048 raw8048Labels permutation346 hz
    mixedMoment B raw8048step0 raw8048step0Labels = mixedMoment B raw8048step1 raw8048step1Labels := by
      have ha : raw8048step1 = (fun i j => raw8048step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8048step1 raw8048step0; decide +kernel
      have hl : raw8048step1Labels = raw8048step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8048step0 raw8048step0Labels permutation34 permutation3
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw8049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8049Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8049step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8049 raw8049Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw8049 raw8049Labels = mixedMoment B raw8049step0 raw8049step0Labels := by
      have hz : ∀ j, raw8049 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8049step0 = (fun i j => raw8049 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8049step0 raw8049; decide +kernel
      have hl : raw8049step0Labels = raw8049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8049 raw8049Labels permutation265 hz
    mixedMoment B raw8049step0 raw8049step0Labels = mixedMoment B raw8049step1 raw8049step1Labels := by
      have ha : raw8049step1 = (fun i j => raw8049step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8049step1 raw8049step0; decide +kernel
      have hl : raw8049step1Labels = raw8049step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8049step0 raw8049step0Labels permutation34 permutation3
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw8050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw8050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw8050step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8050step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw8050step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8050step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw8050step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8050 raw8050Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw8050 raw8050Labels = mixedMoment B raw8050step0 raw8050step0Labels := by
      have hz : ∀ j, raw8050 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8050step0 = (fun i j => raw8050 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8050step0 raw8050; decide +kernel
      have hl : raw8050step0Labels = raw8050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8050 raw8050Labels permutation520 hz
    mixedMoment B raw8050step0 raw8050step0Labels = mixedMoment B raw8050step1 raw8050step1Labels := by
      have hz : ∀ j, raw8050step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8050step1 = (fun i j => raw8050step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8050step1 raw8050step0; decide +kernel
      have hl : raw8050step1Labels = raw8050step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8050step0 raw8050step0Labels permutation80 hz
    mixedMoment B raw8050step1 raw8050step1Labels = mixedMoment B raw8050step2 raw8050step2Labels := by
      have hz : ∀ j, raw8050step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw8050step2 = (fun i j => raw8050step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw8050step2 raw8050step1; decide +kernel
      have hl : raw8050step2Labels = raw8050step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8050step1 raw8050step1Labels permutation14 hz
    mixedMoment B raw8050step2 raw8050step2Labels = mixedMoment B raw8050step3 raw8050step3Labels := by
      have ha : raw8050step3 = (fun i j => raw8050step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8050step3 raw8050step2; decide +kernel
      have hl : raw8050step3Labels = raw8050step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8050step2 raw8050step2Labels permutation2 permutation3
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw8051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8051step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8051step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8051 raw8051Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw8051 raw8051Labels = mixedMoment B raw8051step0 raw8051step0Labels := by
      have hz : ∀ j, raw8051 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8051step0 = (fun i j => raw8051 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8051step0 raw8051; decide +kernel
      have hl : raw8051step0Labels = raw8051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8051 raw8051Labels permutation346 hz
    mixedMoment B raw8051step0 raw8051step0Labels = mixedMoment B raw8051step1 raw8051step1Labels := by
      have hz : ∀ j, raw8051step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8051step1 = (fun i j => raw8051step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8051step1 raw8051step0; decide +kernel
      have hl : raw8051step1Labels = raw8051step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8051step0 raw8051step0Labels permutation56 hz
    mixedMoment B raw8051step1 raw8051step1Labels = mixedMoment B raw8051step2 raw8051step2Labels := by
      have ha : raw8051step2 = (fun i j => raw8051step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8051step2 raw8051step1; decide +kernel
      have hl : raw8051step2Labels = raw8051step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8051step1 raw8051step1Labels permutation13 permutation3
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw8052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8052step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8052 raw8052Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw8052 raw8052Labels = mixedMoment B raw8052step0 raw8052step0Labels := by
      have hz : ∀ j, raw8052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8052step0 = (fun i j => raw8052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8052step0 raw8052; decide +kernel
      have hl : raw8052step0Labels = raw8052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8052 raw8052Labels permutation346 hz
    mixedMoment B raw8052step0 raw8052step0Labels = mixedMoment B raw8052step1 raw8052step1Labels := by
      have hz : ∀ j, raw8052step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8052step1 = (fun i j => raw8052step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8052step1 raw8052step0; decide +kernel
      have hl : raw8052step1Labels = raw8052step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8052step0 raw8052step0Labels permutation56 hz
    mixedMoment B raw8052step1 raw8052step1Labels = mixedMoment B raw8052step2 raw8052step2Labels := by
      have ha : raw8052step2 = (fun i j => raw8052step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8052step2 raw8052step1; decide +kernel
      have hl : raw8052step2Labels = raw8052step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8052step1 raw8052step1Labels permutation9 permutation3
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw8053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8053step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8053 raw8053Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw8053 raw8053Labels = mixedMoment B raw8053step0 raw8053step0Labels := by
      have hz : ∀ j, raw8053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8053step0 = (fun i j => raw8053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8053step0 raw8053; decide +kernel
      have hl : raw8053step0Labels = raw8053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8053 raw8053Labels permutation346 hz
    mixedMoment B raw8053step0 raw8053step0Labels = mixedMoment B raw8053step1 raw8053step1Labels := by
      have ha : raw8053step1 = (fun i j => raw8053step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8053step1 raw8053step0; decide +kernel
      have hl : raw8053step1Labels = raw8053step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8053step0 raw8053step0Labels permutation33 permutation3
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw8054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8054step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8054 raw8054Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw8054 raw8054Labels = mixedMoment B raw8054step0 raw8054step0Labels := by
      have hz : ∀ j, raw8054 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8054step0 = (fun i j => raw8054 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8054step0 raw8054; decide +kernel
      have hl : raw8054step0Labels = raw8054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8054 raw8054Labels permutation265 hz
    mixedMoment B raw8054step0 raw8054step0Labels = mixedMoment B raw8054step1 raw8054step1Labels := by
      have ha : raw8054step1 = (fun i j => raw8054step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8054step1 raw8054step0; decide +kernel
      have hl : raw8054step1Labels = raw8054step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8054step0 raw8054step0Labels permutation33 permutation3
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw8055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8055step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw8055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8055 raw8055Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw8055 raw8055Labels = mixedMoment B raw8055step0 raw8055step0Labels := by
      have hz : ∀ j, raw8055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8055step0 = (fun i j => raw8055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8055step0 raw8055; decide +kernel
      have hl : raw8055step0Labels = raw8055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8055 raw8055Labels permutation346 hz
    mixedMoment B raw8055step0 raw8055step0Labels = mixedMoment B raw8055step1 raw8055step1Labels := by
      have hz : ∀ j, raw8055step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8055step1 = (fun i j => raw8055step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8055step1 raw8055step0; decide +kernel
      have hl : raw8055step1Labels = raw8055step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8055step0 raw8055step0Labels permutation56 hz
    mixedMoment B raw8055step1 raw8055step1Labels = mixedMoment B raw8055step2 raw8055step2Labels := by
      have ha : raw8055step2 = (fun i j => raw8055step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8055step2 raw8055step1; decide +kernel
      have hl : raw8055step2Labels = raw8055step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8055step1 raw8055step1Labels permutation9 permutation3
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw8056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw8056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw8056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw8056step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8056 raw8056Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw8056 raw8056Labels = mixedMoment B raw8056step0 raw8056step0Labels := by
      have hz : ∀ j, raw8056 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8056step0 = (fun i j => raw8056 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8056step0 raw8056; decide +kernel
      have hl : raw8056step0Labels = raw8056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8056 raw8056Labels permutation346 hz
    mixedMoment B raw8056step0 raw8056step0Labels = mixedMoment B raw8056step1 raw8056step1Labels := by
      have hz : ∀ j, raw8056step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8056step1 = (fun i j => raw8056step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8056step1 raw8056step0; decide +kernel
      have hl : raw8056step1Labels = raw8056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8056step0 raw8056step0Labels permutation56 hz
    mixedMoment B raw8056step1 raw8056step1Labels = mixedMoment B raw8056step2 raw8056step2Labels := by
      have ha : raw8056step2 = (fun i j => raw8056step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8056step2 raw8056step1; decide +kernel
      have hl : raw8056step2Labels = raw8056step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8056step1 raw8056step1Labels permutation9 permutation3
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw8057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8057step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8057step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8057step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8057 raw8057Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw8057 raw8057Labels = mixedMoment B raw8057step0 raw8057step0Labels := by
      have hz : ∀ j, raw8057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8057step0 = (fun i j => raw8057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8057step0 raw8057; decide +kernel
      have hl : raw8057step0Labels = raw8057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8057 raw8057Labels permutation346 hz
    mixedMoment B raw8057step0 raw8057step0Labels = mixedMoment B raw8057step1 raw8057step1Labels := by
      have hz : ∀ j, raw8057step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8057step1 = (fun i j => raw8057step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8057step1 raw8057step0; decide +kernel
      have hl : raw8057step1Labels = raw8057step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8057step0 raw8057step0Labels permutation56 hz
    mixedMoment B raw8057step1 raw8057step1Labels = mixedMoment B raw8057step2 raw8057step2Labels := by
      have ha : raw8057step2 = (fun i j => raw8057step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8057step2 raw8057step1; decide +kernel
      have hl : raw8057step2Labels = raw8057step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8057step1 raw8057step1Labels permutation8 permutation3
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw8058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8058 raw8058Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw8058 raw8058Labels = mixedMoment B raw8058step0 raw8058step0Labels := by
      have hz : ∀ j, raw8058 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8058step0 = (fun i j => raw8058 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8058step0 raw8058; decide +kernel
      have hl : raw8058step0Labels = raw8058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8058 raw8058Labels permutation346 hz
    mixedMoment B raw8058step0 raw8058step0Labels = mixedMoment B raw8058step1 raw8058step1Labels := by
      have ha : raw8058step1 = (fun i j => raw8058step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8058step1 raw8058step0; decide +kernel
      have hl : raw8058step1Labels = raw8058step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8058step0 raw8058step0Labels permutation32 permutation3
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw8059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8059 raw8059Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw8059 raw8059Labels = mixedMoment B raw8059step0 raw8059step0Labels := by
      have hz : ∀ j, raw8059 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8059step0 = (fun i j => raw8059 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8059step0 raw8059; decide +kernel
      have hl : raw8059step0Labels = raw8059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8059 raw8059Labels permutation265 hz
    mixedMoment B raw8059step0 raw8059step0Labels = mixedMoment B raw8059step1 raw8059step1Labels := by
      have ha : raw8059step1 = (fun i j => raw8059step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8059step1 raw8059step0; decide +kernel
      have hl : raw8059step1Labels = raw8059step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8059step0 raw8059step0Labels permutation32 permutation3
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw8060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8060step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8060step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw8060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8060 raw8060Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw8060 raw8060Labels = mixedMoment B raw8060step0 raw8060step0Labels := by
      have hz : ∀ j, raw8060 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8060step0 = (fun i j => raw8060 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8060step0 raw8060; decide +kernel
      have hl : raw8060step0Labels = raw8060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8060 raw8060Labels permutation346 hz
    mixedMoment B raw8060step0 raw8060step0Labels = mixedMoment B raw8060step1 raw8060step1Labels := by
      have hz : ∀ j, raw8060step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8060step1 = (fun i j => raw8060step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8060step1 raw8060step0; decide +kernel
      have hl : raw8060step1Labels = raw8060step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8060step0 raw8060step0Labels permutation56 hz
    mixedMoment B raw8060step1 raw8060step1Labels = mixedMoment B raw8060step2 raw8060step2Labels := by
      have ha : raw8060step2 = (fun i j => raw8060step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8060step2 raw8060step1; decide +kernel
      have hl : raw8060step2Labels = raw8060step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8060step1 raw8060step1Labels permutation8 permutation3
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw8061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw8061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw8061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw8061step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8061step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![3, -1, -2]]
def raw8061step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8061step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw8061step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8061 raw8061Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw8061 raw8061Labels = mixedMoment B raw8061step0 raw8061step0Labels := by
      have hz : ∀ j, raw8061 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8061step0 = (fun i j => raw8061 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8061step0 raw8061; decide +kernel
      have hl : raw8061step0Labels = raw8061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8061 raw8061Labels permutation520 hz
    mixedMoment B raw8061step0 raw8061step0Labels = mixedMoment B raw8061step1 raw8061step1Labels := by
      have hz : ∀ j, raw8061step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8061step1 = (fun i j => raw8061step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8061step1 raw8061step0; decide +kernel
      have hl : raw8061step1Labels = raw8061step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8061step0 raw8061step0Labels permutation80 hz
    mixedMoment B raw8061step1 raw8061step1Labels = mixedMoment B raw8061step2 raw8061step2Labels := by
      have hz : ∀ j, raw8061step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw8061step2 = (fun i j => raw8061step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw8061step2 raw8061step1; decide +kernel
      have hl : raw8061step2Labels = raw8061step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8061step1 raw8061step1Labels permutation14 hz
    mixedMoment B raw8061step2 raw8061step2Labels = mixedMoment B raw8061step3 raw8061step3Labels := by
      have ha : raw8061step3 = (fun i j => raw8061step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8061step3 raw8061step2; decide +kernel
      have hl : raw8061step3Labels = raw8061step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8061step2 raw8061step2Labels permutation2 permutation3
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw8062 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw8062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw8062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw8062step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw8062step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8062 raw8062Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw8062 raw8062Labels = mixedMoment B raw8062step0 raw8062step0Labels := by
      have hz : ∀ j, raw8062 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8062step0 = (fun i j => raw8062 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8062step0 raw8062; decide +kernel
      have hl : raw8062step0Labels = raw8062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8062 raw8062Labels permutation265 hz
    mixedMoment B raw8062step0 raw8062step0Labels = mixedMoment B raw8062step1 raw8062step1Labels := by
      have ha : raw8062step1 = (fun i j => raw8062step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8062step1 raw8062step0; decide +kernel
      have hl : raw8062step1Labels = raw8062step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8062step0 raw8062step0Labels permutation38 permutation7
    mixedMoment B raw8062step1 raw8062step1Labels = mixedMoment B raw8062step2 raw8062step2Labels := by
      have ha : raw8062step2 = raw8062step1 := by apply Matrix.ext; unfold raw8062step2 raw8062step1; decide +kernel
      have hl : raw8062step1Labels = labelEmbedding10 ∘ raw8062step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8062step1 raw8062step1Labels raw8062step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw8063 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8063 raw8063Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw8063 raw8063Labels = mixedMoment B raw8063step0 raw8063step0Labels := by
      have hz : ∀ j, raw8063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8063step0 = (fun i j => raw8063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8063step0 raw8063; decide +kernel
      have hl : raw8063step0Labels = raw8063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8063 raw8063Labels permutation346 hz
    mixedMoment B raw8063step0 raw8063step0Labels = mixedMoment B raw8063step1 raw8063step1Labels := by
      have hz : ∀ j, raw8063step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8063step1 = (fun i j => raw8063step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8063step1 raw8063step0; decide +kernel
      have hl : raw8063step1Labels = raw8063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8063step0 raw8063step0Labels permutation56 hz
    mixedMoment B raw8063step1 raw8063step1Labels = mixedMoment B raw8063step2 raw8063step2Labels := by
      have ha : raw8063step2 = (fun i j => raw8063step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8063step2 raw8063step1; decide +kernel
      have hl : raw8063step2Labels = raw8063step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8063step1 raw8063step1Labels permutation31 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
